$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_b4: the least possible numerator degree after differentiating
  p(x)/(x^3-x) 1992 times, for the specified coprime real polynomials, is
  3984. Derivatives are taken on the rational function's natural domain,
  excluding the poles -1, 0, and 1, and equality with f/g is required
  wherever both rational functions are defined. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P92B4Poly is set.mm's finite-support univariate polynomial ring over the
  reals, P92B4Q is x^3-x in that ring, and P92B4Domain is its natural real
  domain. P92B4Valid says that p is nonzero, has no coefficient in degree
  1992 or above, and is coprime to P92B4Q. Coprimality is expressed by the
  equivalent Bezout identity over RR[x].

  Set.mm's native RR Dn operator iterates the partial real derivative. The
  domain condition requires the source quotient to be 1992-times
  differentiable at every point of P92B4Domain. P92B4Pair compares that
  derivative with f/g exactly where both rational functions are defined:
  x lies in P92B4Domain and g(x) is nonzero. The denominator g must also be a
  nonzero polynomial. No arbitrary totalized values are imposed at poles.

  P92B4Degree(f,k) says that k is the exact degree of the nonzero polynomial
  f. The final assertion is the explicit IsLeast characterization at the
  ground-truth solution annotation 3984: that degree is attained, and it is
  no greater than any other attainable numerator degree. All declarations
  are unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c P92B4Poly P92B4Q P92B4Domain P92B4Valid P92B4Pair P92B4Degree $.

p92b4-poly-syntax $a class P92B4Poly $.
p92b4-q-syntax $a class P92B4Q $.
p92b4-domain-syntax $a class P92B4Domain $.
p92b4-valid-syntax $a wff ( P92B4Valid p ) $.
p92b4-pair-syntax $a wff ( P92B4Pair p f ) $.
p92b4-degree-syntax $a wff ( P92B4Degree f k ) $.

p92b4-poly-definition $a |- P92B4Poly =
  ( Base ` ( Poly1 ` RRfld ) ) $.

p92b4-q-definition $a |- P92B4Q =
  (
    (
      3
      ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) )
      ( var1 ` RRfld )
    )
    ( -g ` ( Poly1 ` RRfld ) )
    ( var1 ` RRfld )
  ) $.

p92b4-domain-definition $a |- P92B4Domain =
  ( RR \ { -u 1 , 0 , 1 } ) $.

${
  $d a p $.
  $d b p $.
  $d j p $.

  p92b4-valid-definition $a |- (
    ( P92B4Valid p )
    <->
    (
      p =/= ( 0g ` ( Poly1 ` RRfld ) )
      /\
      (
        A. j e. NN0
          (
            ; ; ; 1 9 9 2 <_ j
            ->
            ( ( coe1 ` p ) ` j ) = 0
          )
        /\
        E. a e. P92B4Poly E. b e. P92B4Poly
          (
            (
              (
                a
                ( .r ` ( Poly1 ` RRfld ) )
                p
              )
              ( +g ` ( Poly1 ` RRfld ) )
              (
                b
                ( .r ` ( Poly1 ` RRfld ) )
                P92B4Q
              )
            )
            =
            ( 1r ` ( Poly1 ` RRfld ) )
          )
      )
    )
  ) $.
$}

${
  $d f g $.
  $d f x $.
  $d g p $.
  $d g x $.
  $d p x $.

  p92b4-pair-definition $a |- (
    ( P92B4Pair p f )
    <->
    E. g e. P92B4Poly
      (
        g =/= ( 0g ` ( Poly1 ` RRfld ) )
        /\
        (
          P92B4Domain
          C_
          dom
          (
            (
              RR
              Dn
              (
                x e. P92B4Domain |->
                  (
                    ( ( ( eval1 ` RRfld ) ` p ) ` x )
                    /
                    ( ( x ^ 3 ) - x )
                  )
              )
            )
            `
            ; ; ; 1 9 9 2
          )
          /\
          A. x e. P92B4Domain
            (
              ( ( ( eval1 ` RRfld ) ` g ) ` x ) =/= 0
              ->
              (
                (
                  (
                    RR
                    Dn
                    (
                      x e. P92B4Domain |->
                        (
                          ( ( ( eval1 ` RRfld ) ` p ) ` x )
                          /
                          ( ( x ^ 3 ) - x )
                        )
                    )
                  )
                  `
                  ; ; ; 1 9 9 2
                )
                `
                x
              )
              =
              (
                ( ( ( eval1 ` RRfld ) ` f ) ` x )
                /
                ( ( ( eval1 ` RRfld ) ` g ) ` x )
              )
            )
        )
      )
  ) $.
$}

${
  $d f j $.
  $d f k $.
  $d j k $.

  p92b4-degree-definition $a |- (
    ( P92B4Degree f k )
    <->
    (
      ( ( coe1 ` f ) ` k ) =/= 0
      /\
      A. j e. NN0
        (
          k < j
          ->
          ( ( coe1 ` f ) ` j ) = 0
        )
    )
  ) $.
$}

${
  $d f k $.
  $d k p $.

  putnambench-putnam-1992-b4 $a |- (
    E. p e. P92B4Poly E. f e. P92B4Poly
      (
        ( P92B4Valid p )
        /\
        (
          ( P92B4Pair p f )
          /\
          ( P92B4Degree f ; ; ; 3 9 8 4 )
        )
      )
    /\
    A. k e. NN0
      (
        E. p e. P92B4Poly E. f e. P92B4Poly
          (
            ( P92B4Valid p )
            /\
            (
              ( P92B4Pair p f )
              /\
              ( P92B4Degree f k )
            )
          )
        ->
        ; ; ; 3 9 8 4 <_ k
      )
  ) $.
$}
