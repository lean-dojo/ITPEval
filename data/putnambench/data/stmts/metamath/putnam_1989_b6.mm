$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1989_b6: the expected right-endpoint Riemann sum over uniformly
  ordered points in the unit interval is represented by integration against
  a degree-n polynomial bounded between zero and one. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P89B6Index(n) is {1,...,n}, and P89B6Region(n) is the full open region of
  strictly increasing real coordinate functions on that index set.
  P89B6Ext(X,n) extends X by x_0 = 0 and x_(n+1) = 1.

  P89B6Integrand(F,n) is the source right-endpoint Riemann sum on the ordered
  region and zero off that region. Its Bochner integral against voln divided
  by the volume of the region is therefore exactly the source uniform
  expectation. Poly, deg, and function application are set.mm's native real
  polynomial representation, exact degree, and evaluation.

  The polynomial witness is quantified before F, so it is independent of
  the continuous function. Every declaration is an unproved $a statement;
  this database contains no $p proof statement.
$)

$c P89B6Index P89B6Region P89B6Ext P89B6Sum $.
$c P89B6Integrand P89B6Expectation $.

p89b6-index-syntax $a class ( P89B6Index n ) $.
p89b6-region-syntax $a class ( P89B6Region n ) $.
p89b6-ext-syntax $a class ( P89B6Ext X n ) $.
p89b6-sum-syntax $a class ( P89B6Sum F X n ) $.
p89b6-integrand-syntax $a class ( P89B6Integrand F n ) $.
p89b6-expectation-syntax $a class ( P89B6Expectation F n ) $.

p89b6-index-definition $a |- (
  P89B6Index n
) = (
  1 ... n
) $.

${
  $d X i j n $.

  p89b6-region-definition $a |- (
    P89B6Region n
  ) = {
    X e. ( RR ^m ( P89B6Index n ) ) |
      (
        A. i e. ( P89B6Index n )
          (
            0 < ( X ` i )
            /\
            ( X ` i ) < 1
          )
        /\
        A. i e. ( P89B6Index n )
          A. j e. ( P89B6Index n )
            (
              i < j
              ->
              ( X ` i ) < ( X ` j )
            )
      )
  } $.
$}

${
  $d X i n $.

  p89b6-ext-definition $a |- (
    P89B6Ext X n
  ) = (
    i e. ( 0 ... ( n + 1 ) ) |->
      if (
        i = 0 ,
        0 ,
        if (
          i = ( n + 1 ) ,
          1 ,
          ( X ` i )
        )
      )
  ) $.
$}

${
  $d F X i n $.

  p89b6-sum-definition $a |- (
    P89B6Sum F X n
  ) = (
    sum_ i e. ( 0 ... n )
      (
        (
          (
            ( P89B6Ext X n )
            `
            ( i + 1 )
          )
          -
          (
            ( P89B6Ext X n )
            `
            i
          )
        )
        x.
        (
          F
          `
          (
            ( P89B6Ext X n )
            `
            ( i + 1 )
          )
        )
      )
  ) $.
$}

${
  $d F X n $.

  p89b6-integrand-definition $a |- (
    P89B6Integrand F n
  ) = (
    X e. ( RR ^m ( P89B6Index n ) ) |->
      if (
        X e. ( P89B6Region n ) ,
        ( P89B6Sum F X n ) ,
        0
      )
  ) $.
$}

p89b6-expectation-definition $a |- (
  P89B6Expectation F n
) = (
  (
    (
      RRfld
      itgm
      ( voln ` ( P89B6Index n ) )
    )
    `
    ( P89B6Integrand F n )
  )
  /
  (
    ( voln ` ( P89B6Index n ) )
    `
    ( P89B6Region n )
  )
) $.

${
  $d F P n t $.

  putnambench-putnam-1989-b6 $a |-
    A. n e. NN
      E. P e. ( Poly ` RR )
        (
          ( deg ` P ) = n
          /\
          (
            A. t e. ( 0 [,] 1 )
              (
                0 <_ ( P ` t )
                /\
                ( P ` t ) <_ 1
              )
            /\
            A. F e. ( RR ^m RR )
              (
                (
                  ( F ` 1 ) = 0
                  /\
                  (
                    ( F |` ( 0 [,] 1 ) )
                    e.
                    ( ( 0 [,] 1 ) -cn-> RR )
                  )
                )
                ->
                (
                  P89B6Expectation F n
                )
                =
                S. ( 0 [,] 1 )
                  (
                    ( F ` t )
                    x.
                    ( P ` t )
                  )
                  _d t
              )
          )
        )
  $.
$}
