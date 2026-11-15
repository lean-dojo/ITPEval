$(
  Statement-only formalization of "The Four Color Problem" from Hundred
  Theorems item 032: every simple planar map over an arbitrary model of the
  real line is colorable with at most four colors. This file contains no proof.
$)

$[ library/set.mm $]

$(
  This encoding preserves the definitions used by the Rocq source rather than
  replacing them with uninterpreted predicates.

  HT032RealModel codes Real.model as a nine-component function whose entries
  are the carrier, order, supremum, addition, zero, opposite, multiplication,
  one, and inverse. Its definition includes exactly the source typing
  conditions and sixteen real-model axioms. Points are ordered pairs in the
  carrier square, regions are subsets of that plane, and maps are functions
  from points to regions.

  HT032PlainMap, HT032AtMost, HT032Open, HT032Connected, HT032SimpleMap,
  HT032FiniteSimpleMap, HT032Closure, HT032CornerMap, HT032NotCorner,
  HT032Adjacent, HT032Coloring, and HT032ColorableWith are direct
  set-theoretic renderings of the correspondingly named definitions in
  realplane.v. In particular, colors remain equivalence-relation regions, and
  adjacency uses a non-corner point in the common closures of two regions.

  The two final assertions preserve the finite intermediate theorem and the
  full compactness theorem. They are unproved $a assertions; this statement
  file adds no $p proof statement.
$)

$c HT032Val HT032Le HT032Sup HT032Add HT032Zero HT032Opp $.
$c HT032Mul HT032One HT032Inv HT032Eq HT032HasSup HT032RealModel $.
$c HT032Plane HT032Map HT032PlainMap HT032AtMost HT032Open $.
$c HT032Connected HT032SimpleMap HT032FiniteSimpleMap HT032Closure $.
$c HT032CornerMap HT032NotCorner HT032Adjacent HT032Coloring $.
$c HT032ColorableWith $.

ht032-val-syntax $a class ( HT032Val R ) $.
ht032-le-syntax $a class ( HT032Le R ) $.
ht032-sup-syntax $a class ( HT032Sup R ) $.
ht032-add-syntax $a class ( HT032Add R ) $.
ht032-zero-syntax $a class ( HT032Zero R ) $.
ht032-opp-syntax $a class ( HT032Opp R ) $.
ht032-mul-syntax $a class ( HT032Mul R ) $.
ht032-one-syntax $a class ( HT032One R ) $.
ht032-inv-syntax $a class ( HT032Inv R ) $.
ht032-eq-syntax $a wff ( HT032Eq R X Y ) $.
ht032-has-sup-syntax $a wff ( HT032HasSup R A ) $.
ht032-real-model-syntax $a wff ( HT032RealModel R ) $.
ht032-plane-syntax $a class ( HT032Plane R ) $.
ht032-map-syntax $a wff ( HT032Map R M ) $.
ht032-plain-map-syntax $a wff ( HT032PlainMap R M ) $.
ht032-at-most-syntax $a wff ( HT032AtMost R N M ) $.
ht032-open-syntax $a wff ( HT032Open R A ) $.
ht032-connected-syntax $a wff ( HT032Connected R A ) $.
ht032-simple-map-syntax $a wff ( HT032SimpleMap R M ) $.
ht032-finite-simple-map-syntax $a wff ( HT032FiniteSimpleMap R M ) $.
ht032-closure-syntax $a class ( HT032Closure R A ) $.
ht032-corner-map-syntax $a class ( HT032CornerMap R M Z ) $.
ht032-not-corner-syntax $a class ( HT032NotCorner R M ) $.
ht032-adjacent-syntax $a wff ( HT032Adjacent R M X Y ) $.
ht032-coloring-syntax $a wff ( HT032Coloring R M K ) $.
ht032-colorable-with-syntax $a wff ( HT032ColorableWith R N M ) $.

 ${
  ht032-val-definition $a |- ( HT032Val R ) = ( R ` 0 ) $.
  ht032-le-definition $a |- ( HT032Le R ) = ( R ` 1 ) $.
  ht032-sup-definition $a |- ( HT032Sup R ) = ( R ` 2 ) $.
  ht032-add-definition $a |- ( HT032Add R ) = ( R ` 3 ) $.
  ht032-zero-definition $a |- ( HT032Zero R ) = ( R ` 4 ) $.
  ht032-opp-definition $a |- ( HT032Opp R ) = ( R ` 5 ) $.
  ht032-mul-definition $a |- ( HT032Mul R ) = ( R ` 6 ) $.
  ht032-one-definition $a |- ( HT032One R ) = ( R ` 7 ) $.
  ht032-inv-definition $a |- ( HT032Inv R ) = ( R ` 8 ) $.
$}

${
  $d R X Y $.
  ht032-eq-definition $a |- (
    ( HT032Eq R X Y )
    <->
    (
      <. X , Y >. e. ( HT032Le R )
      /\
      <. Y , X >. e. ( HT032Le R )
    )
  ) $.
$}

${
  $d A R x y $.
  ht032-has-sup-definition $a |- (
    ( HT032HasSup R A )
    <->
    (
      A =/= (/)
      /\
      E. x e. ( HT032Val R )
        A. y e. A <. y , x >. e. ( HT032Le R )
    )
  ) $.
$}

${
  $d a R x y z $.

  ht032-real-model-definition $a |- (
    ( HT032RealModel R )
    <->
    (
      (
        R : ( 0 ..^ 9 ) --> _V
        /\
        (
          ( HT032Le R )
          C_
          ( ( HT032Val R ) X. ( HT032Val R ) )
        )
      )
      /\
      (
        (
          ( HT032Sup R ) : ~P ( HT032Val R ) --> ( HT032Val R )
          /\
          (
            ( HT032Add R )
            :
            ( ( HT032Val R ) X. ( HT032Val R ) )
            -->
            ( HT032Val R )
          )
        )
        /\
        (
          (
            ( HT032Zero R ) e. ( HT032Val R )
            /\
            ( HT032Opp R ) : ( HT032Val R ) --> ( HT032Val R )
          )
          /\
          (
            (
              ( HT032Mul R )
              :
              ( ( HT032Val R ) X. ( HT032Val R ) )
              -->
              ( HT032Val R )
            )
            /\
            (
              (
                ( HT032One R ) e. ( HT032Val R )
                /\
                ( HT032Inv R ) : ( HT032Val R ) --> ( HT032Val R )
              )
              /\
              (
                (
                  A. x e. ( HT032Val R )
                    <. x , x >. e. ( HT032Le R )
                  /\
                  A. x e. ( HT032Val R )
                    A. y e. ( HT032Val R )
                      A. z e. ( HT032Val R )
                        (
                          (
                            <. x , y >. e. ( HT032Le R )
                            /\
                            <. y , z >. e. ( HT032Le R )
                          )
                          ->
                          <. x , z >. e. ( HT032Le R )
                        )
                )
                /\
                (
                  (
                    A. a e. ~P ( HT032Val R )
                      (
                        ( HT032HasSup R a )
                        ->
                        A. x e. a
                          <. x , ( ( HT032Sup R ) ` a ) >.
                            e. ( HT032Le R )
                      )
                    /\
                    A. a e. ~P ( HT032Val R )
                      A. x e. ( HT032Val R )
                        (
                          ( HT032HasSup R a )
                          ->
                          (
                            E. y e. a
                              <. x , y >. e. ( HT032Le R )
                            \/
                            <. ( ( HT032Sup R ) ` a ) , x >.
                              e. ( HT032Le R )
                          )
                        )
                  )
                  /\
                  (
                    (
                      A. x e. ( HT032Val R )
                        A. y e. ( HT032Val R )
                          A. z e. ( HT032Val R )
                            (
                              <. y , z >. e. ( HT032Le R )
                              ->
                              <.
                                ( ( HT032Add R ) ` <. x , y >. ) ,
                                ( ( HT032Add R ) ` <. x , z >. )
                              >. e. ( HT032Le R )
                            )
                      /\
                      A. x e. ( HT032Val R )
                        A. y e. ( HT032Val R )
                          (
                            HT032Eq
                            R
                            ( ( HT032Add R ) ` <. x , y >. )
                            ( ( HT032Add R ) ` <. y , x >. )
                          )
                    )
                    /\
                    (
                      (
                        A. x e. ( HT032Val R )
                          A. y e. ( HT032Val R )
                            A. z e. ( HT032Val R )
                              (
                                HT032Eq
                                R
                                (
                                  ( HT032Add R )
                                  `
                                  <.
                                    x ,
                                    ( ( HT032Add R ) ` <. y , z >. )
                                  >.
                                )
                                (
                                  ( HT032Add R )
                                  `
                                  <.
                                    ( ( HT032Add R ) ` <. x , y >. ) ,
                                    z
                                  >.
                                )
                              )
                        /\
                        A. x e. ( HT032Val R )
                          (
                            HT032Eq
                            R
                            (
                              ( HT032Add R )
                              `
                              <. ( HT032Zero R ) , x >.
                            )
                            x
                          )
                      )
                      /\
                      (
                        (
                          A. x e. ( HT032Val R )
                            (
                              HT032Eq
                              R
                              (
                                ( HT032Add R )
                                `
                                <. x , ( ( HT032Opp R ) ` x ) >.
                              )
                              ( HT032Zero R )
                            )
                          /\
                          A. x e. ( HT032Val R )
                            A. y e. ( HT032Val R )
                              A. z e. ( HT032Val R )
                                (
                                  (
                                    <. ( HT032Zero R ) , x >.
                                      e. ( HT032Le R )
                                    /\
                                    <. y , z >. e. ( HT032Le R )
                                  )
                                  ->
                                  <.
                                    ( ( HT032Mul R ) ` <. x , y >. ) ,
                                    ( ( HT032Mul R ) ` <. x , z >. )
                                  >. e. ( HT032Le R )
                                )
                        )
                        /\
                        (
                          (
                            A. x e. ( HT032Val R )
                              A. y e. ( HT032Val R )
                                (
                                  HT032Eq
                                  R
                                  ( ( HT032Mul R ) ` <. x , y >. )
                                  ( ( HT032Mul R ) ` <. y , x >. )
                                )
                            /\
                            A. x e. ( HT032Val R )
                              A. y e. ( HT032Val R )
                                A. z e. ( HT032Val R )
                                  (
                                    HT032Eq
                                    R
                                    (
                                      ( HT032Mul R )
                                      `
                                      <.
                                        x ,
                                        ( ( HT032Mul R ) ` <. y , z >. )
                                      >.
                                    )
                                    (
                                      ( HT032Mul R )
                                      `
                                      <.
                                        ( ( HT032Mul R ) ` <. x , y >. ) ,
                                        z
                                      >.
                                    )
                                  )
                          )
                          /\
                          (
                            (
                              A. x e. ( HT032Val R )
                                A. y e. ( HT032Val R )
                                  A. z e. ( HT032Val R )
                                    (
                                      HT032Eq
                                      R
                                      (
                                        ( HT032Mul R )
                                        `
                                        <.
                                          x ,
                                          (
                                            ( HT032Add R )
                                            `
                                            <. y , z >.
                                          )
                                        >.
                                      )
                                      (
                                        ( HT032Add R )
                                        `
                                        <.
                                          (
                                            ( HT032Mul R )
                                            `
                                            <. x , y >.
                                          ) ,
                                          (
                                            ( HT032Mul R )
                                            `
                                            <. x , z >.
                                          )
                                        >.
                                      )
                                    )
                              /\
                              A. x e. ( HT032Val R )
                                (
                                  HT032Eq
                                  R
                                  (
                                    ( HT032Mul R )
                                    `
                                    <. ( HT032One R ) , x >.
                                  )
                                  x
                                )
                            )
                            /\
                            (
                              (
                                A. x e. ( HT032Val R )
                                  (
                                    -. ( HT032Eq R x ( HT032Zero R ) )
                                    ->
                                    (
                                      HT032Eq
                                      R
                                      (
                                        ( HT032Mul R )
                                        `
                                        <. x , ( ( HT032Inv R ) ` x ) >.
                                      )
                                      ( HT032One R )
                                    )
                                  )
                                /\
                                -. (
                                  HT032Eq
                                  R
                                  ( HT032One R )
                                  ( HT032Zero R )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}

 ${
  ht032-plane-definition $a |- (
    ( HT032Plane R )
    =
    ( ( HT032Val R ) X. ( HT032Val R ) )
  ) $.
$}

${
  $d M R $.
  ht032-map-definition $a |- (
    ( HT032Map R M )
    <->
    (
      M
      :
      ( HT032Plane R )
      -->
      ~P ( HT032Plane R )
    )
  ) $.
$}

${
  $d M R x y z $.
  ht032-plain-map-definition $a |- (
    ( HT032PlainMap R M )
    <->
    (
      ( HT032Map R M )
      /\
      (
        A. x e. ( HT032Plane R )
          A. y e. ( HT032Plane R )
            (
              y e. ( M ` x )
              ->
              x e. ( M ` y )
            )
        /\
        A. x e. ( HT032Plane R )
          A. y e. ( HT032Plane R )
            (
              y e. ( M ` x )
              ->
              A. z e. ( M ` y ) z e. ( M ` x )
            )
      )
    )
  ) $.
$}

${
  $d f M N R x y $.
  ht032-at-most-definition $a |- (
    ( HT032AtMost R N M )
    <->
    (
      N e. NN0
      /\
      E. f
        (
          f : ( 0 ..^ N ) --> ( HT032Plane R )
          /\
          A. x e. ( HT032Plane R )
            (
              x e. ( M ` x )
              ->
              E. y e. ( 0 ..^ N ) x e. ( M ` ( f ` y ) )
            )
        )
    )
  ) $.
$}

${
  $d A b R w x y z $.
  ht032-open-definition $a |- (
    ( HT032Open R A )
    <->
    (
      A C_ ( HT032Plane R )
      /\
      A. z e. A
        E. w e. ( HT032Val R )
          E. x e. ( HT032Val R )
            E. y e. ( HT032Val R )
              E. b e. ( HT032Val R )
                (
                  (
                    (
                      -. <. ( 1st ` z ) , w >. e. ( HT032Le R )
                      /\
                      -. <. x , ( 1st ` z ) >. e. ( HT032Le R )
                    )
                    /\
                    (
                      -. <. ( 2nd ` z ) , y >. e. ( HT032Le R )
                      /\
                      -. <. b , ( 2nd ` z ) >. e. ( HT032Le R )
                    )
                  )
                  /\
                  A. z e. ( HT032Plane R )
                    (
                      (
                        (
                          -. <. ( 1st ` z ) , w >. e. ( HT032Le R )
                          /\
                          -. <. x , ( 1st ` z ) >. e. ( HT032Le R )
                        )
                        /\
                        (
                          -. <. ( 2nd ` z ) , y >. e. ( HT032Le R )
                          /\
                          -. <. b , ( 2nd ` z ) >. e. ( HT032Le R )
                        )
                      )
                      ->
                      z e. A
                    )
                )
    )
  ) $.
$}

${
  $d A b c R x $.
  ht032-connected-definition $a |- (
    ( HT032Connected R A )
    <->
    (
      A C_ ( HT032Plane R )
      /\
      A. b e. ~P ( HT032Plane R )
        A. c e. ~P ( HT032Plane R )
          (
            (
              (
                ( HT032Open R b )
                /\
                ( HT032Open R c )
              )
              /\
              (
                (
                  A C_ ( b u. c )
                  /\
                  E. x e. A x e. b
                )
                /\
                E. x e. A x e. c
              )
            )
            ->
            E. x e. b x e. c
          )
    )
  ) $.
$}

${
  $d M R x $.
  ht032-simple-map-definition $a |- (
    ( HT032SimpleMap R M )
    <->
    (
      ( HT032PlainMap R M )
      /\
      A. x e. ( HT032Plane R )
        (
          ( HT032Open R ( M ` x ) )
          /\
          ( HT032Connected R ( M ` x ) )
        )
    )
  ) $.
$}

${
  $d M n R $.
  ht032-finite-simple-map-definition $a |- (
    ( HT032FiniteSimpleMap R M )
    <->
    (
      ( HT032SimpleMap R M )
      /\
      E. n e. NN0 ( HT032AtMost R n M )
    )
  ) $.
$}

${
  $d A b R x y $.
  ht032-closure-definition $a |- (
    ( HT032Closure R A )
    =
    { x e. ( HT032Plane R ) |
      A. b e. ~P ( HT032Plane R )
        (
          (
            ( HT032Open R b )
            /\
            x e. b
          )
          ->
          E. y e. A y e. b
        )
    }
  ) $.
$}

${
  $d M R x y Z $.
  ht032-corner-map-definition $a |- (
    ( HT032CornerMap R M Z )
    =
    (
      x e. ( HT032Plane R )
      |->
      { y e. ( HT032Plane R ) |
        (
          y e. ( M ` x )
          /\
          Z e. ( HT032Closure R ( M ` x ) )
        )
      }
    )
  ) $.
$}

${
  $d M R z $.
  ht032-not-corner-definition $a |- (
    ( HT032NotCorner R M )
    =
    { z e. ( HT032Plane R ) |
      (
        HT032AtMost
        R
        2
        ( HT032CornerMap R M z )
      )
    }
  ) $.
$}

${
  $d M R w X Y $.
  ht032-adjacent-definition $a |- (
    ( HT032Adjacent R M X Y )
    <->
    (
      -. Y e. ( M ` X )
      /\
      E. w e. ( HT032Plane R )
        (
          w e. ( HT032NotCorner R M )
          /\
          (
            w e. ( HT032Closure R ( M ` X ) )
            /\
            w e. ( HT032Closure R ( M ` Y ) )
          )
        )
    )
  ) $.
$}

${
  $d K M R x y $.
  ht032-coloring-definition $a |- (
    ( HT032Coloring R M K )
    <->
    (
      ( HT032PlainMap R K )
      /\
      (
        (
          A. x e. ( HT032Plane R )
            (
              x e. ( K ` x )
              ->
              x e. ( M ` x )
            )
          /\
          A. x e. ( HT032Plane R )
            A. y e. ( M ` x ) y e. ( K ` x )
        )
        /\
        A. x e. ( HT032Plane R )
          A. y e. ( HT032Plane R )
            (
              ( HT032Adjacent R M x y )
              ->
              -. y e. ( K ` x )
            )
      )
    )
  ) $.
$}

${
  $d k M N R $.
  ht032-colorable-with-definition $a |- (
    ( HT032ColorableWith R N M )
    <->
    E. k
      (
        ( HT032Coloring R M k )
        /\
        ( HT032AtMost R N k )
      )
  ) $.
$}

${
  $d m r $.

  hundred-theorems-032-four-color-finite $a |- (
    A. r
      (
        ( HT032RealModel r )
        ->
        A. m
          (
            ( HT032Map r m )
            ->
            (
              ( HT032FiniteSimpleMap r m )
              ->
              ( HT032ColorableWith r 4 m )
            )
          )
      )
  ) $.

  hundred-theorems-032-four-color $a |- (
    A. r
      (
        ( HT032RealModel r )
        ->
        A. m
          (
            ( HT032Map r m )
            ->
            (
              ( HT032SimpleMap r m )
              ->
              ( HT032ColorableWith r 4 m )
            )
          )
      )
  ) $.
$}
