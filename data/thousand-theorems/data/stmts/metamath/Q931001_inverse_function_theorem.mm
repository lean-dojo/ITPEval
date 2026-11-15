$(
  Statement-only formalization of Thousand Theorems corpus artifact Q931001
  (thousand-theorems__metamath__Q931001), "Inverse function theorem": a
  function between arbitrary normed spaces over an arbitrary nontrivially
  normed field, with complete source space and an invertible strict Frechet
  derivative at a point, has a locally constructed inverse whose strict
  derivative at the image point is the inverse linear equivalence. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q931001HasStrictFDerivAt is the two-point epsilon-delta definition of a
  strict Frechet derivative between arbitrary normed spaces.
  Q931001ValidData explicitly unpacks the continuous linear equivalence into
  mutually inverse continuous linear maps L and M. This is equivalent to
  Lean's bundled E equivL[K] F object, with M representing its symm field.
  Completeness is required only of E, exactly as in the source theorem.

  Q931001OperatorNorm is the operator norm of M. Q931001ApproximatesOn and
  Q931001OpenApproxNeighborhoods expand the approximation neighborhood used
  by HasStrictFDerivAt.toOpenPartialHomeomorph, with constant
  ||M||^-1 / 2. The constant is explicitly zero when ||M|| is zero, matching
  NNReal's totalized inverse in the degenerate zero-space case.

  The approximation neighborhood N, a default point d of E, and a choice
  function h are existentially scoped inside the final assertion. For each
  y, Q931001InverseFiber is its preimage in N when nonempty and the singleton
  {d} otherwise. Q931001InverseFiberFamily is the set-sized range of this
  family, and Q931001ChoiceFunction has exactly SetMM's ac5 form on that set.
  Thus Q931001InvFunOn expands Function.invFunOn without introducing a global
  choice selector, and Q931001LocalInverse is definitionally this total
  inverse function. The final unproved $a assertion renders
  HasStrictFDerivAt.to_localInverse and contains no $p proof statement.
$)

$c Q931001HasStrictFDerivAt Q931001ValidData Q931001OperatorNorm
   Q931001ApproximatesOn Q931001OpenApproxNeighborhoods
   Q931001InverseFiber Q931001InverseFiberMap
   Q931001InverseFiberFamily Q931001ChoiceFunction
   Q931001InvFunOn Q931001LocalInverse $.

q931001-has-strict-fderiv-at-syntax $a wff
  ( Q931001HasStrictFDerivAt V W f L a ) $.
q931001-valid-data-syntax $a wff
  ( Q931001ValidData K E F f L M a ) $.
q931001-operator-norm-syntax $a class
  ( Q931001OperatorNorm E F M ) $.
q931001-approximates-on-syntax $a wff
  ( Q931001ApproximatesOn E F f L S c ) $.
q931001-open-approx-neighborhoods-syntax $a class
  ( Q931001OpenApproxNeighborhoods E F f L M a ) $.
q931001-inverse-fiber-syntax $a class
  ( Q931001InverseFiber E F f N d y ) $.
q931001-inverse-fiber-map-syntax $a class
  ( Q931001InverseFiberMap E F f N d ) $.
q931001-inverse-fiber-family-syntax $a class
  ( Q931001InverseFiberFamily E F f N d ) $.
q931001-choice-function-syntax $a wff
  ( Q931001ChoiceFunction E F f N d h ) $.
q931001-inv-fun-on-syntax $a class
  ( Q931001InvFunOn E F f N d h ) $.
q931001-local-inverse-syntax $a class
  ( Q931001LocalInverse E F f N d h ) $.

${
  $d L V W a d e f x y $.

  q931001-has-strict-fderiv-at-definition $a |- (
    ( Q931001HasStrictFDerivAt V W f L a )
    <->
    (
      (
        f e. ( ( Base ` W ) ^m ( Base ` V ) )
        /\
        a e. ( Base ` V )
        /\
        L e. ( V LMHom W )
        /\
        L e. ( ( TopOpen ` V ) Cn ( TopOpen ` W ) )
      )
      /\
      A. e e. RR+
        E. d e. RR+
          A. x e. ( Base ` V )
            A. y e. ( Base ` V )
              (
                (
                  (
                    ( norm ` V )
                    `
                    (
                      x
                      ( +g ` V )
                      ( ( -g ` V ) ` a )
                    )
                  )
                  <
                  d
                  /\
                  (
                    ( norm ` V )
                    `
                    (
                      y
                      ( +g ` V )
                      ( ( -g ` V ) ` a )
                    )
                  )
                  <
                  d
                )
                ->
                (
                  ( norm ` W )
                  `
                  (
                    (
                      ( f ` y )
                      ( +g ` W )
                      ( ( -g ` W ) ` ( f ` x ) )
                    )
                    ( +g ` W )
                    (
                      ( -g ` W )
                      `
                      (
                        L
                        `
                        (
                          y
                          ( +g ` V )
                          ( ( -g ` V ) ` x )
                        )
                      )
                    )
                  )
                )
                <_
                (
                  e
                  x.
                  (
                    ( norm ` V )
                    `
                    (
                      y
                      ( +g ` V )
                      ( ( -g ` V ) ` x )
                    )
                  )
                )
              )
    )
  ) $.
$}

${
  $d E F K L M a c f x y $.

  q931001-valid-data-definition $a |- (
    ( Q931001ValidData K E F f L M a )
    <->
    (
      K e. ( NrmRing i^i Field )
      /\
      E e. { x e. NrmVec | ( Scalar ` x ) = K }
      /\
      F e. { y e. NrmVec | ( Scalar ` y ) = K }
      /\
      E. c e. ( Base ` K )
        1 < ( ( norm ` K ) ` c )
      /\
      E e. CMetSp
      /\
      L e. ( E LMHom F )
      /\
      M e. ( F LMHom E )
      /\
      M e. ( ( TopOpen ` F ) Cn ( TopOpen ` E ) )
      /\
      A. x e. ( Base ` E )
        ( M ` ( L ` x ) ) = x
      /\
      A. y e. ( Base ` F )
        ( L ` ( M ` y ) ) = y
      /\
      ( Q931001HasStrictFDerivAt E F f L a )
    )
  ) $.
$}

${
  $d C E F M y $.

  q931001-operator-norm-definition $a |- (
    Q931001OperatorNorm E F M
  ) = inf (
    {
      C e. RR |
      (
        0 <_ C
        /\
        A. y e. ( Base ` F )
          (
            ( norm ` E )
            `
            ( M ` y )
          )
          <_
          (
            C
            x.
            ( ( norm ` F ) ` y )
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
  $d E F L S c f x y $.

  q931001-approximates-on-definition $a |- (
    ( Q931001ApproximatesOn E F f L S c )
    <->
    A. x e. S
      A. y e. S
        (
          ( norm ` F )
          `
          (
            (
              ( f ` y )
              ( +g ` F )
              ( ( -g ` F ) ` ( f ` x ) )
            )
            ( +g ` F )
            (
              ( -g ` F )
              `
              (
                L
                `
                (
                  y
                  ( +g ` E )
                  ( ( -g ` E ) ` x )
                )
              )
            )
          )
        )
        <_
        (
          c
          x.
          (
            ( norm ` E )
            `
            (
              y
              ( +g ` E )
              ( ( -g ` E ) ` x )
            )
          )
        )
  ) $.
$}

${
  $d E F L M a f s $.

  q931001-open-approx-neighborhoods-definition $a |- (
    Q931001OpenApproxNeighborhoods E F f L M a
  ) =
    { s e. ~P ( Base ` E ) |
      (
        a e. s
        /\
        s e. ( TopOpen ` E )
        /\
        (
          Q931001ApproximatesOn E F f L s
          if (
            ( Q931001OperatorNorm E F M ) = 0
            ,
            0
            ,
            (
              (
                1
                /
                ( Q931001OperatorNorm E F M )
              )
              /
              2
            )
          )
        )
      )
    }
  $.
$}

${
  $d E F N d f x y $.

  q931001-inverse-fiber-definition $a |- (
    Q931001InverseFiber E F f N d y
  ) =
    if
    (
      { x e. N | ( f ` x ) = y } =/= (/) ,
      { x e. N | ( f ` x ) = y } ,
      { d }
    )
  $.
$}

${
  $d E F N d f y $.

  q931001-inverse-fiber-map-definition $a |- (
    Q931001InverseFiberMap E F f N d
  ) =
    (
      y e. ( Base ` F ) |->
      ( Q931001InverseFiber E F f N d y )
    )
  $.
$}

${
  $d E F N d f $.

  q931001-inverse-fiber-family-definition $a |- (
    Q931001InverseFiberFamily E F f N d
  ) =
    ran ( Q931001InverseFiberMap E F f N d )
  $.
$}

${
  $d E F N S d f h $.

  q931001-choice-function-definition $a |- (
    Q931001ChoiceFunction E F f N d h
  )
  <->
    (
      h Fn ( Q931001InverseFiberFamily E F f N d )
      /\
      A. S e. ( Q931001InverseFiberFamily E F f N d )
        ( h ` S ) e. S
    )
  $.
$}

${
  $d E F N d f h y $.

  q931001-inv-fun-on-definition $a |- (
    Q931001InvFunOn E F f N d h
  ) =
    (
      y e. ( Base ` F ) |->
      (
        h
        `
        ( Q931001InverseFiber E F f N d y )
      )
    )
  $.
$}

${
  $d E F N d f h $.

  q931001-local-inverse-definition $a |- (
    Q931001LocalInverse E F f N d h
  ) =
    ( Q931001InvFunOn E F f N d h )
  $.
$}

${
  $d E F K L M N a d f h $.

  thousand-theorems-q931001-inverse-function-theorem $a |-
    A. K A. E A. F A. f A. L A. M A. a
      (
        (
          Q931001ValidData K E F f L M a
        )
        ->
        E. N e.
          ( Q931001OpenApproxNeighborhoods E F f L M a )
          E. d e. ( Base ` E )
            E. h
              (
                (
                  Q931001ChoiceFunction E F f N d h
                )
                /\
                (
                  Q931001HasStrictFDerivAt
                  F
                  E
                  ( Q931001LocalInverse E F f N d h )
                  M
                  ( f ` a )
                )
              )
      )
  $.
$}
