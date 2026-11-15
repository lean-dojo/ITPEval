$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2016_a1: the least positive derivative order for which every
  integer-coefficient polynomial evaluates to a multiple of 2016 at every
  integer is eight. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` ZZring ) is Set.mm's ring of all finite-support
  univariate polynomials over the integers. P16A1Der is its formal
  derivative, obtained from the native power-series derivative mPSDer, and
  IterComp gives the j-fold derivative, including order zero.

  P16A1Property(j) quantifies over every integer-coefficient polynomial and
  every integer evaluation point and requires divisibility by 2016. The
  final conjunction says that 8 is a positive order satisfying this property
  and is no greater than any other positive natural satisfying it. This is
  the explicit attained-minimum form of the source IsLeast/LEAST statement.
  All declarations are unproved $a statement encodings; there is no $p proof
  declaration in this file.
$)

$c P16A1Der P16A1Property $.

p16a1-der-syntax $a class P16A1Der $.
p16a1-property-syntax $a wff ( P16A1Property j ) $.

p16a1-der-definition $a |- P16A1Der =
  (
    p e. ( Base ` ( Poly1 ` ZZring ) ) |->
      ( ( ( 1o mPSDer ZZring ) ` (/) ) ` p )
  ) $.

${
  $d j k $.
  $d j p $.
  $d k p $.

  p16a1-property-definition $a |- (
    ( P16A1Property j )
    <->
    A. p e. ( Base ` ( Poly1 ` ZZring ) )
      A. k e. ZZ
        ( ; ; ; 2 0 1 6 ) ||
        (
          (
            ( eval1 ` ZZring )
            `
            (
              (
                ( IterComp ` P16A1Der )
                `
                j
              )
              `
              p
            )
          )
          `
          k
        )
  ) $.
$}

putnambench-putnam-2016-a1 $a |- (
  (
    0 < 8
    /\
    ( P16A1Property 8 )
  )
  /\
  A. j e. NN0
    (
      (
        0 < j
        /\
        ( P16A1Property j )
      )
      ->
      8 <_ j
    )
) $.
