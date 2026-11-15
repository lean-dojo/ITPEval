$(
  Statement-only formalization of Thousand Theorems corpus artifact Q859122
  (thousand-theorems__metamath__Q859122), "Cauchy-Hadamard theorem": for a
  formal multilinear series over an arbitrary nontrivially normed field, the
  inverse of its convergence radius is the limsup of the nth roots of its
  coefficient norms. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q859122Multilinear gives the set-theoretic content of a continuous
  multilinear map from the finite power indexed by 0 ..^ n. Linearity is
  stated one coordinate at a time, and the product-of-norms estimate is the
  standard equivalent characterization of continuity. Q859122Series is
  therefore exactly a FormalMultilinearSeries.

  Q859122OpNorm is exactly Mathlib's continuous-multilinear-map operator norm:
  the infimum of all nonnegative real constants C giving the global bound
  ||L(x)|| <= C * product_i ||x_i||. Q859122Radius is exactly Mathlib's radius
  definition: the supremum of nonnegative finite r for which ||P_n|| r^n is
  bounded by one real constant for every n.

  Q859122Root uses Mathlib's NNReal real-power conventions. In particular its
  n = 0 value is one, including when the coefficient norm is zero.
  Q859122ENNInv is inversion on the extended nonnegative reals, with zero and
  positive infinity interchanged. SetMM's limsup of the resulting nonnegative
  real sequence is extended-real-valued, matching the ENNReal limsup in the
  canonical Lean statement.

  The final declaration quantifies over arbitrary bundled normed fields,
  normed spaces, and formal multilinear series. The element of norm greater
  than one is the explicit SetMM rendering of NontriviallyNormedField. Every
  preceding $a declaration is syntax or a faithful definition, and the final
  $a declaration is the unproved corpus statement; there is no $p proof.
$)

$c Q859122Update Q859122Multilinear Q859122Series Q859122OpNorm
   Q859122Radius Q859122Root Q859122ENNInv $.

q859122-update-syntax
  $a class ( Q859122Update x i y ) $.
q859122-multilinear-syntax
  $a wff ( Q859122Multilinear K E F n L ) $.
q859122-series-syntax
  $a wff ( Q859122Series K E F P ) $.
q859122-op-norm-syntax
  $a class ( Q859122OpNorm E F n L ) $.
q859122-radius-syntax
  $a class ( Q859122Radius E F P ) $.
q859122-root-syntax
  $a class ( Q859122Root x n ) $.
q859122-enn-inv-syntax
  $a class ( Q859122ENNInv x ) $.

${
  $d i j x y $.

  q859122-update-definition $a |- (
    Q859122Update x i y
  ) = (
    j e. dom x |->
      if ( j = i , y , ( x ` j ) )
  ) $.
$}

${
  $d C E F K L a i j n x y $.

  q859122-multilinear-definition $a |- (
    ( Q859122Multilinear K E F n L )
    <->
    (
      L :
        ( ( Base ` E ) ^m ( 0 ..^ n ) )
        -->
        ( Base ` F )
      /\
      A. i e. ( 0 ..^ n )
        A. x e. ( ( Base ` E ) ^m ( 0 ..^ n ) )
          A. y e. ( ( Base ` E ) ^m ( 0 ..^ n ) )
            (
              L
              `
              (
                Q859122Update
                x i
                (
                  ( x ` i )
                  ( +g ` E )
                  ( y ` i )
                )
              )
            )
            =
            (
              ( L ` x )
              ( +g ` F )
              (
                L
                `
                ( Q859122Update x i ( y ` i ) )
              )
            )
      /\
      A. i e. ( 0 ..^ n )
        A. a e. ( Base ` K )
          A. x e. ( ( Base ` E ) ^m ( 0 ..^ n ) )
            (
              L
              `
              (
                Q859122Update
                x i
                (
                  a
                  ( .s ` E )
                  ( x ` i )
                )
              )
            )
            =
            (
              a
              ( .s ` F )
              ( L ` x )
            )
      /\
      E. C e. RR
        (
          0 <_ C
          /\
          A. x e. ( ( Base ` E ) ^m ( 0 ..^ n ) )
            (
              ( ( norm ` F ) ` ( L ` x ) )
              <_
              (
                C
                x.
                prod_ j e. ( 0 ..^ n )
                  ( ( norm ` E ) ` ( x ` j ) )
              )
            )
        )
    )
  ) $.
$}

${
  $d E F K P L n $.

  q859122-series-definition $a |- (
    ( Q859122Series K E F P )
    <->
    (
      P Fn NN0
      /\
      A. n e. NN0
        ( Q859122Multilinear K E F n ( P ` n ) )
    )
  ) $.
$}

${
  $d C E F L j n x $.

  q859122-op-norm-definition $a |- (
    Q859122OpNorm E F n L
  ) = inf (
    {
      C e. RR |
      (
        0 <_ C
        /\
        A. x e. ( ( Base ` E ) ^m ( 0 ..^ n ) )
          (
            ( ( norm ` F ) ` ( L ` x ) )
            <_
            (
              C
              x.
              prod_ j e. ( 0 ..^ n )
                ( ( norm ` E ) ` ( x ` j ) )
            )
          )
      )
    }
    ,
    RR
    ,
    <
  ) $.
$}

${
  $d C E F P n r $.

  q859122-radius-definition $a |- (
    Q859122Radius E F P
  ) = sup (
    { r e. RR |
      (
        0 <_ r
        /\
        E. C e. RR
          A. n e. NN0
            (
              (
                Q859122OpNorm E F n ( P ` n )
              )
              x.
              ( r ^ n )
            )
            <_
            C
      )
    } ,
    RR* ,
    <
  ) $.
$}

${
  $d n x $.

  q859122-root-definition $a |- (
    Q859122Root x n
  ) = if (
    n = 0 ,
    1 ,
    if (
      x = 0 ,
      0 ,
      (
        exp
        `
        (
          ( log ` x )
          x.
          ( 1 / n )
        )
      )
    )
  ) $.
$}

${
  q859122-enn-inv-definition $a |- (
    Q859122ENNInv x
  ) = if (
    x = 0 ,
    +oo ,
    if ( x = +oo , 0 , ( 1 / x ) )
  ) $.
$}

${
  $d E F K P c n $.

  thousand-theorems-q859122-cauchy-hadamard $a |-
    A. K e. ( NrmRing i^i Field )
      A. E e. { e e. NrmVec | ( Scalar ` e ) = K }
        A. F e. { e e. NrmVec | ( Scalar ` e ) = K }
          (
            E. c e. ( Base ` K )
              1 < ( ( norm ` K ) ` c )
            ->
            A. P
              (
                ( Q859122Series K E F P )
                ->
                (
                  Q859122ENNInv
                  ( Q859122Radius E F P )
                )
                =
                (
                  limsup
                  `
                  (
                    n e. NN0 |->
                      (
                        Q859122Root
                        (
                          Q859122OpNorm E F n ( P ` n )
                        )
                        n
                      )
                  )
                )
              )
          )
  $.
$}
