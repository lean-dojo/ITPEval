$(
  Statement-only formalization of PutnamBench artifact putnam_1965_b1:
  convergence of the finite-dimensional unit-cube integrals of a squared
  cosine of the normalized coordinate sum to the specified real solution
  constant. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P65B1Index n is the coordinate set {0,...,n}, canonically representing
  Fin (n+1). P65B1Cube n is the full unit cube in the corresponding real
  function space. P65B1Integrand n is the source integrand extended by zero
  outside that cube, so its real measure integral against voln is exactly the
  source set integral.

  The limit arrow is sequential convergence of the NN0-indexed real-valued
  integral sequence. The published answer is stated explicitly as 1/2.
  Every declaration below is an unproved $a statement, and this database
  contains no $p proof statement.
$)

$c P65B1Index P65B1Cube P65B1Integrand P65B1Integral $.

p65b1-index-syntax $a class ( P65B1Index N ) $.
p65b1-cube-syntax $a class ( P65B1Cube N ) $.
p65b1-integrand-syntax $a class ( P65B1Integrand N ) $.
p65b1-integral-syntax $a class ( P65B1Integral N ) $.

p65b1-index-definition $a |- (
  P65B1Index N
) = (
  0 ... N
) $.

${
  $d K N X $.

  p65b1-cube-definition $a |- (
    P65B1Cube N
  ) = {
    X e. ( RR ^m ( P65B1Index N ) ) |
      A. K e. ( P65B1Index N )
        (
          0 <_ ( X ` K )
          /\
          ( X ` K ) <_ 1
        )
  } $.
$}

${
  $d K N X $.

  p65b1-integrand-definition $a |- (
    P65B1Integrand N
  ) = (
    X e. ( RR ^m ( P65B1Index N ) ) |->
      if (
        X e. ( P65B1Cube N ) ,
        (
          cos
          `
          (
            (
              _pi
              /
              ( 2 x. ( N + 1 ) )
            )
            x.
            (
              sum_ K e. ( P65B1Index N )
                ( X ` K )
            )
          )
        )
        ^ 2
        ,
        0
      )
  ) $.
$}

p65b1-integral-definition $a |- (
  P65B1Integral N
) = (
  (
    RRfld
    itgm
    ( voln ` ( P65B1Index N ) )
  )
  `
  ( P65B1Integrand N )
) $.

putnambench-putnam-1965-b1 $a |- (
  N e. NN0 |->
    ( P65B1Integral N )
)
~~>
( 1 / 2 )
$.
