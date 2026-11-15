$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1990_b1: classification of the continuously differentiable real
  functions whose squared value equals 1990 plus the oriented integral of
  the sum of the squares of the function and its derivative. The solutions
  are the two functions x |-> plus or minus sqrt(1990) exp(x). This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions. Membership in
  ( ( C^n ` RR ) ` 1 ) is set.mm's native assertion of global continuous
  differentiability through order one, and ( ( RR Dn F ) ` 1 ) is its real
  derivative.

  P90B1Integral F x is the oriented Lebesgue integral from zero to x of
  F(t)^2 + F'(t)^2. For nonnegative x it integrates over (0,x); for negative
  x it is the negative of the integral over (x,0). Endpoint inclusion is
  immaterial for these continuous integrands, so this is equivalent to the
  source interval integral for every real x.

  The final biconditional inlines the explicit two-function solution set.
  Every declaration below is an unproved $a statement encoding; this
  database contains no $p proof statement.
$)

$c P90B1Integral $.

p90b1-integral-syntax $a class ( P90B1Integral F x ) $.

${
  $d F t x $.

  p90b1-integral-definition $a |- (
    P90B1Integral F x
  ) = if (
    0 <_ x ,
    S. ( 0 (,) x )
      (
        ( ( F ` t ) ^ 2 )
        +
        ( ( ( ( RR Dn F ) ` 1 ) ` t ) ^ 2 )
      )
      _d t ,
    -u
    S. ( x (,) 0 )
      (
        ( ( F ` t ) ^ 2 )
        +
        ( ( ( ( RR Dn F ) ` 1 ) ` t ) ^ 2 )
      )
      _d t
  ) $.
$}

${
  $d F x $.

  putnambench-putnam-1990-b1 $a |- A. F e. ( RR ^m RR )
    (
      (
        F e. ( ( C^n ` RR ) ` 1 )
        /\
        A. x e. RR
          ( ( F ` x ) ^ 2 )
          =
          (
            ( P90B1Integral F x )
            +
            ; ; ; 1 9 9 0
          )
      )
      <->
      (
        F
        =
        (
          x e. RR |->
            (
              ( sqrt ` ; ; ; 1 9 9 0 )
              x.
              ( exp ` x )
            )
        )
        \/
        F
        =
        (
          x e. RR |->
            (
              -u
              (
                ( sqrt ` ; ; ; 1 9 9 0 )
                x.
                ( exp ` x )
              )
            )
        )
      )
    )
  $.
$}
