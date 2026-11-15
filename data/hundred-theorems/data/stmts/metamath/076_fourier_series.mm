$(
  Statement-only formalization of "Fourier Series" from Hundred Theorems
  corpus artifact 076. It states that the normalized real trigonometric
  Fourier partial sums of every square-integrable real function on
  [-pi,pi] converge to that function in the L2 norm. This file contains no
  proof.
$)

$[ library/set.mm $]

$(
  The interval C below is (-pi,pi); replacing the closed source interval by
  this open interval does not change square-integrability, Fourier
  coefficients, or L2 convergence because the two endpoints have Lebesgue
  measure zero.

  HT076Basis is exactly the source basis in its source ordering:

    k = 0       : 1 / sqrt(2*pi)
    k = 2*j+1   : sin((j+1)*x) / sqrt(pi)
    k = 2*j+2   : cos((j+1)*x) / sqrt(pi).

  HT076Coeff is the Lebesgue integral of f times a basis element, and
  HT076Partial is the sum over 0 <= k < n. HT076SquareIntegrable says that
  the restriction of f to C is measurable and that its square is Lebesgue
  integrable there. The conclusion is the epsilon-N expansion of convergence
  of the squared-error integral to zero, which is equivalent to convergence
  in the L2 norm.

  All four definitions and the final theorem declaration are unproved $a
  statements; this database contains no $p proof statements.
$)

$c HT076Basis HT076Coeff HT076Partial HT076SquareIntegrable $.

ht076-basis-syntax $a class ( HT076Basis K X ) $.
ht076-coeff-syntax $a class ( HT076Coeff F K ) $.
ht076-partial-syntax $a class ( HT076Partial F N X ) $.
ht076-square-integrable-syntax $a wff ( HT076SquareIntegrable F ) $.

${
  $d j K $.
  $d j X $.

  ht076-basis-definition $a |- (
    ( HT076Basis K X )
    =
    if
      (
        K = 0 ,
        ( 1 / ( sqrt ` ( 2 x. _pi ) ) ) ,
        if
          (
            E. j e. NN0 K = ( ( 2 x. j ) + 1 ) ,
            (
              ( sin ` ( ( ( K + 1 ) / 2 ) x. X ) )
              /
              ( sqrt ` _pi )
            ) ,
            (
              ( cos ` ( ( K / 2 ) x. X ) )
              /
              ( sqrt ` _pi )
            )
          )
      )
  ) $.
$}

${
  $d x F $.
  $d x K $.

  ht076-coeff-definition $a |- (
    ( HT076Coeff F K )
    =
    S. ( -u _pi (,) _pi )
      ( ( F ` x ) x. ( HT076Basis K x ) )
      _d x
  ) $.
$}

${
  $d k F $.
  $d k N $.
  $d k X $.

  ht076-partial-definition $a |- (
    ( HT076Partial F N X )
    =
    sum_ k e. ( 0 ..^ N )
      ( ( HT076Coeff F k ) x. ( HT076Basis k X ) )
  ) $.
$}

${
  $d x F $.

  ht076-square-integrable-definition $a |- (
    ( HT076SquareIntegrable F )
    <->
    (
      F : RR --> RR
      /\
      (
        ( F |` ( -u _pi (,) _pi ) ) e. MblFn
        /\
        (
          x e. ( -u _pi (,) _pi )
          |->
          ( ( F ` x ) ^ 2 )
        )
        e. L^1
      )
    )
  ) $.
$}

${
  $d e F $.
  $d m F $.
  $d n F $.
  $d x F $.
  $d x n $.

  hundred-theorems-076-fourier-series $a |- (
    ( HT076SquareIntegrable F )
    ->
    A. e e. RR
      (
        0 < e
        ->
        E. m e. NN0
          A. n e. NN0
            (
              m <_ n
              ->
              S. ( -u _pi (,) _pi )
                (
                  (
                    ( F ` x )
                    -
                    ( HT076Partial F n x )
                  )
                  ^ 2
                )
                _d x
                < e
            )
      )
  ) $.
$}
