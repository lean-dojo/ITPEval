$(
  Statement-only formalization of Thousand Theorems corpus artifact Q842953
  (thousand-theorems__metamath__Q842953), "Lebesgue's density theorem": in a
  second-countable Borel metric space with the Besicovitch covering property,
  almost every point of an arbitrary set for a locally finite measure is a
  density point, as measured by closed balls of radii tending to zero from
  above. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q842953ClosedBall is the metric closed ball. Q842953Measure evaluates the
  outer measure induced by a measure, so arbitrary subsets are retained.
  Q842953RestrictedOuter is exactly the outer-measure value of the restriction
  of M to S: it takes the infimum of M(T intersect S) over measurable
  supersets T.

  Q842953EDiv is extended-nonnegative division with Lean's total conventions.
  Q842953DensityTendsto expands convergence of the density quotient to one
  along positive real radii tending to zero. Q842953HasBesicovitch expands the
  source covering property by excluding a finite satellite configuration.

  All declarations below are syntax, bidirectional definitions, or the final
  unproved $a statement. There are no $p declarations in this file.
$)

$c Q842953ClosedBall Q842953Measure Q842953RestrictedOuter
   Q842953EDiv Q842953DensityTendsto Q842953Satellite
   Q842953HasBesicovitch Q842953LocallyFinite $.

q842953-closed-ball-syntax $a
  class ( Q842953ClosedBall D X x r ) $.
q842953-measure-syntax $a
  class ( Q842953Measure M A ) $.
q842953-restricted-outer-syntax $a
  class ( Q842953RestrictedOuter M S A ) $.
q842953-ediv-syntax $a
  class ( Q842953EDiv A B ) $.
q842953-density-tendsto-syntax $a
  wff ( Q842953DensityTendsto M D S x ) $.
q842953-satellite-syntax $a
  wff ( Q842953Satellite D X N t c r ) $.
q842953-has-besicovitch-syntax $a
  wff ( Q842953HasBesicovitch D X ) $.
q842953-locally-finite-syntax $a
  wff ( Q842953LocallyFinite M J ) $.

${
  $d D X r x y $.

  q842953-closed-ball-definition $a |- (
    Q842953ClosedBall D X x r
  ) =
    { y e. X | ( x D y ) <_ r }
  $.
$}

${
  $d A M $.

  q842953-measure-definition $a |- (
    Q842953Measure M A
  ) =
    ( ( toOMeas ` M ) ` A )
  $.
$}

${
  $d A M S T z $.

  q842953-restricted-outer-definition $a |- (
    Q842953RestrictedOuter M S A
  ) =
    inf
    (
      { z e. RR* |
        E. T e. dom M
          (
            A C_ T
            /\
            z = ( Q842953Measure M ( T i^i S ) )
          )
      } ,
      RR* ,
      <
    )
  $.
$}

${
  $d A B $.

  q842953-ediv-definition $a |- (
    Q842953EDiv A B
  ) =
    if (
      B = 0 ,
      if ( A = 0 , 0 , +oo ) ,
      if (
        B = +oo ,
        0 ,
        if ( A = +oo , +oo , ( A / B ) )
      )
    )
  $.
$}

${
  $d A D M S U X e r x $.

  q842953-density-tendsto-definition $a |- (
    ( Q842953DensityTendsto M D S x )
    <->
    A. U e.
      ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
      (
        1 e. U
        ->
        E. e e. RR
          (
            0 < e
            /\
            A. r e. RR
              (
                ( 0 < r /\ r < e )
                ->
                (
                  Q842953EDiv
                  (
                    Q842953Measure
                    M
                    (
                      S i^i
                      (
                        Q842953ClosedBall
                        D
                        ( U. dom M )
                        x
                        r
                      )
                    )
                  )
                  (
                    Q842953Measure
                    M
                    (
                      Q842953ClosedBall
                      D
                      ( U. dom M )
                      x
                      r
                    )
                  )
                ) e. U
              )
          )
      )
  ) $.
$}

${
  $d D X N t c r i j $.

  q842953-satellite-definition $a |- (
    ( Q842953Satellite D X N t c r )
    <->
    (
      c e. ( X ^m ( 0 ..^ ( N + 1 ) ) )
      /\
      (
        r e. ( RR ^m ( 0 ..^ ( N + 1 ) ) )
        /\
        (
          A. i e. ( 0 ..^ ( N + 1 ) )
            0 < ( r ` i )
          /\
          (
            A. i e. ( 0 ..^ ( N + 1 ) )
              A. j e. ( 0 ..^ ( N + 1 ) )
                (
                  i =/= j
                  ->
                  (
                    (
                      ( r ` i ) <_ ( ( c ` i ) D ( c ` j ) )
                      /\
                      ( r ` j ) <_ ( t x. ( r ` i ) )
                    )
                    \/
                    (
                      ( r ` j ) <_ ( ( c ` j ) D ( c ` i ) )
                      /\
                      ( r ` i ) <_ ( t x. ( r ` j ) )
                    )
                  )
                )
            /\
            (
              A. i e. ( 0 ..^ N )
                (
                  ( r ` i ) <_ ( ( c ` i ) D ( c ` N ) )
                  /\
                  ( r ` N ) <_ ( t x. ( r ` i ) )
                )
              /\
              A. i e. ( 0 ..^ N )
                (
                  ( ( c ` i ) D ( c ` N ) )
                  <_
                  ( ( r ` i ) + ( r ` N ) )
                )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d D X N t c r $.

  q842953-has-besicovitch-definition $a |- (
    ( Q842953HasBesicovitch D X )
    <->
    E. N e. NN0
      E. t e. RR
        (
          1 < t
          /\
          -. E. c e. ( X ^m ( 0 ..^ ( N + 1 ) ) )
            E. r e. ( RR ^m ( 0 ..^ ( N + 1 ) ) )
              ( Q842953Satellite D X N t c r )
        )
  ) $.
$}

${
  $d J M U x $.

  q842953-locally-finite-definition $a |- (
    ( Q842953LocallyFinite M J )
    <->
    A. x e. U. dom M
      E. U e. J
        (
          x e. U
          /\
          ( M ` U ) < +oo
        )
  ) $.
$}

${
  $d A B D J M N S T U X c e i j r s t x y z $.

  thousand-theorems-q842953-lebesgue-density-theorem $a |-
    A. M e. U. ran measures
      A. D
        A. s
          (
            (
              D e. ( Met ` ( U. dom M ) )
              /\
              (
                ( MetOpen ` D ) e. 2ndc
                /\
                (
                  dom M = ( sigaGen ` ( MetOpen ` D ) )
                  /\
                  (
                    ( Q842953LocallyFinite M ( MetOpen ` D ) )
                    /\
                    (
                      Q842953HasBesicovitch
                      D
                      ( U. dom M )
                    )
                  )
                )
              )
            )
            ->
            (
              s C_ ( U. dom M )
              ->
              (
                Q842953RestrictedOuter
                M
                s
                {
                  x e. ( U. dom M ) |
                    -. ( Q842953DensityTendsto M D s x )
                }
              ) = 0
            )
          )
  $.
$}
