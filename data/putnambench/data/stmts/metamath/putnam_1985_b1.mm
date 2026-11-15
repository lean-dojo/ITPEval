$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1985_b1: the five distinct integers -2, -1, 0, 1, and 2 minimize
  the number of nonzero coefficients of the product of the corresponding
  five monic linear real polynomials among all five distinct integers.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The half-open ordinal interval 0 ..^ 5 is the carrier Fin 5, and
  P85B1Solution is the source solution i |-> i - 2. P85B1Poly maps an
  arbitrary integer-valued function on that carrier to the product
  prod_i (X - m_i) in set.mm's finite-support univariate polynomial ring
  over the real field. The integer values are canonically real and algSc
  embeds them as constant polynomials.

  P85B1Nnz is the cardinality of the support of the complete NN0-indexed
  coefficient function. Every polynomial has finite support, and every
  P85B1Poly value is monic and nonzero, so this is exactly the source count
  over indices through natDegree/degree. The final assertion requires the
  displayed solution to be injective and compares its count with every
  injective integer-valued function on Fin 5.

  All declarations below are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c P85B1Solution P85B1Poly P85B1Nnz $.

p85b1-solution-syntax $a class P85B1Solution $.
p85b1-poly-syntax $a class P85B1Poly $.
p85b1-nnz-syntax $a class P85B1Nnz $.

${
  p85b1-solution-definition $a |- P85B1Solution =
    ( i e. ( 0 ..^ 5 ) |-> ( i - 2 ) ) $.
$}

${
  p85b1-poly-definition $a |- P85B1Poly =
    (
      m e. ( ZZ ^m ( 0 ..^ 5 ) ) |->
        (
          (
            (
              (
                (
                  ( var1 ` RRfld )
                  ( -g ` ( Poly1 ` RRfld ) )
                  (
                    ( algSc ` ( Poly1 ` RRfld ) )
                    `
                    ( m ` 0 )
                  )
                )
                ( .r ` ( Poly1 ` RRfld ) )
                (
                  ( var1 ` RRfld )
                  ( -g ` ( Poly1 ` RRfld ) )
                  (
                    ( algSc ` ( Poly1 ` RRfld ) )
                    `
                    ( m ` 1 )
                  )
                )
              )
              ( .r ` ( Poly1 ` RRfld ) )
              (
                ( var1 ` RRfld )
                ( -g ` ( Poly1 ` RRfld ) )
                (
                  ( algSc ` ( Poly1 ` RRfld ) )
                  `
                  ( m ` 2 )
                )
              )
            )
            ( .r ` ( Poly1 ` RRfld ) )
            (
              ( var1 ` RRfld )
              ( -g ` ( Poly1 ` RRfld ) )
              (
                ( algSc ` ( Poly1 ` RRfld ) )
                `
                ( m ` 3 )
              )
            )
          )
          ( .r ` ( Poly1 ` RRfld ) )
          (
            ( var1 ` RRfld )
            ( -g ` ( Poly1 ` RRfld ) )
            (
              ( algSc ` ( Poly1 ` RRfld ) )
              `
              ( m ` 4 )
            )
          )
        )
    ) $.
$}

${
  $d j p $.

  p85b1-nnz-definition $a |- P85B1Nnz =
    (
      p e. ( Base ` ( Poly1 ` RRfld ) ) |->
        (
          # `
          {
            j e. NN0 |
            ( ( coe1 ` p ) ` j ) =/= 0
          }
        )
    ) $.
$}

${
  putnambench-putnam-1985-b1 $a |- (
    P85B1Solution : ( 0 ..^ 5 ) -1-1-> ZZ
    /\
    A. m e. ( ZZ ^m ( 0 ..^ 5 ) )
      (
        m : ( 0 ..^ 5 ) -1-1-> ZZ
        ->
        (
          P85B1Nnz
          `
          ( P85B1Poly ` P85B1Solution )
        )
        <_
        (
          P85B1Nnz
          `
          ( P85B1Poly ` m )
        )
      )
  ) $.
$}
