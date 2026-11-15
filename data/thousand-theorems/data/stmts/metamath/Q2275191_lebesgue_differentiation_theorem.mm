$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2275191
  (thousand-theorems__metamath__Q2275191), "Lebesgue differentiation
  theorem": for an almost-everywhere measurable extended-nonnegative
  function with finite lower integral, its normalized integrals over the
  sets of a Vitali family converge to the function almost everywhere.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The definitions below expand the structures used by Lean's
  VitaliFamily.ae_tendsto_lintegral_div.  Q2275191PseudoMetric restricts
  SetMM's extended pseudometrics to finite real distances, matching Lean's
  PseudoMetricSpace.  Every topological notion below uses the pseudometric
  topology ( topGen ` ran ( ball ` D ) ) generated directly by its balls.
  Q2275191VitaliFamily includes measurability, nonempty interior, arbitrarily
  small closed sets, and the full covering axiom for arbitrary subfamilies.
  Q2275191TendstoAt uses the closed-ball basis that characterizes
  VitaliFamily.filterAt.  The lower integral, restriction to a set,
  almost-everywhere measurability, local finiteness, and total
  extended-nonnegative division are explicit.

  All declarations are syntax, bidirectional definitions, or the final
  unproved $a statement.  There are no $p declarations in this file.
$)

$c Q2275191PseudoMetric Q2275191ClosedBall Q2275191Measure Q2275191LocallyFinite
   Q2275191VitaliFamily Q2275191Simple Q2275191SimpleIntegral
   Q2275191LIntegral Q2275191SetLIntegral Q2275191AEMeasurable
   Q2275191EDiv Q2275191TendstoAt $.

q2275191-pseudometric-syntax $a
  wff ( Q2275191PseudoMetric D X ) $.
q2275191-closed-ball-syntax $a
  class ( Q2275191ClosedBall D X x e ) $.
q2275191-measure-syntax $a
  class ( Q2275191Measure M A ) $.
q2275191-locally-finite-syntax $a
  wff ( Q2275191LocallyFinite M J ) $.
q2275191-vitali-family-syntax $a
  wff ( Q2275191VitaliFamily M D V ) $.
q2275191-simple-syntax $a
  wff ( Q2275191Simple M G ) $.
q2275191-simple-integral-syntax $a
  class ( Q2275191SimpleIntegral M G ) $.
q2275191-lintegral-syntax $a
  class ( Q2275191LIntegral M H ) $.
q2275191-set-lintegral-syntax $a
  class ( Q2275191SetLIntegral M H A ) $.
q2275191-aemeasurable-syntax $a
  wff ( Q2275191AEMeasurable M H ) $.
q2275191-ediv-syntax $a
  class ( Q2275191EDiv A B ) $.
q2275191-tendsto-at-syntax $a
  wff ( Q2275191TendstoAt M D V H x z ) $.

${
  $d D X $.

  q2275191-pseudometric-definition $a |- (
    ( Q2275191PseudoMetric D X )
    <->
    (
      D e. ( PsMet ` X )
      /\
      D e. ( RR ^m ( X X. X ) )
    )
  ) $.
$}

${
  $d D X e x y $.

  q2275191-closed-ball-definition $a |- (
    Q2275191ClosedBall D X x e
  ) =
    { y e. X | ( x D y ) <_ e }
  $.
$}

${
  $d A M $.

  q2275191-measure-definition $a |- (
    Q2275191Measure M A
  ) =
    ( ( toOMeas ` M ) ` A )
  $.
$}

${
  $d J M U x $.

  q2275191-locally-finite-definition $a |- (
    ( Q2275191LocallyFinite M J )
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
  $d A D M T U V X e f p q s x $.

  q2275191-vitali-family-definition $a |- (
    ( Q2275191VitaliFamily M D V )
    <->
    (
      V e. ( ( ~P ( ~P ( U. dom M ) ) ) ^m ( U. dom M ) )
      /\
      (
        A. x e. U. dom M
          A. A e. ( V ` x )
            (
              A e. dom M
              /\
              E. U e. ( topGen ` ran ( ball ` D ) )
                (
                  U =/= (/)
                  /\
                  U C_ A
                )
            )
        /\
        (
          A. x e. U. dom M
            A. e e. RR
              (
                0 < e
                ->
                E. A e. ( V ` x )
                  A C_ (
                    Q2275191ClosedBall D ( U. dom M ) x e
                  )
              )
          /\
          A. s e. ~P ( U. dom M )
            A. f e.
              ( ( ~P ( ~P ( U. dom M ) ) ) ^m ( U. dom M ) )
              (
                (
                  A. x e. s
                    ( f ` x ) C_ ( V ` x )
                  /\
                  A. x e. s
                    A. e e. RR
                      (
                        0 < e
                        ->
                        E. A e. ( f ` x )
                          A C_ (
                            Q2275191ClosedBall
                            D
                            ( U. dom M )
                            x
                            e
                          )
                      )
                )
                ->
                E. T e.
                  ~P ( ( U. dom M ) X. ~P ( U. dom M ) )
                  (
                    A. p e. T
                      ( 1st ` p ) e. s
                    /\
                    (
                      A. p e. T
                        A. q e. T
                          (
                            p =/= q
                            ->
                            (
                              ( 2nd ` p ) i^i ( 2nd ` q )
                            ) = (/)
                          )
                      /\
                      (
                        A. p e. T
                          ( 2nd ` p ) e. ( f ` ( 1st ` p ) )
                        /\
                        (
                          Q2275191Measure
                          M
                          (
                            s
                            \
                            U_ p e. T ( 2nd ` p )
                          )
                        ) = 0
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
  $d G M $.

  q2275191-simple-definition $a |- (
    ( Q2275191Simple M G )
    <->
    (
      G : U. dom M --> ( 0 [,] +oo )
      /\
      (
        G e.
          (
            dom M
            MblFnM
            (
              sigaGen `
              ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
            )
          )
        /\
        ran G e. Fin
      )
    )
  ) $.
$}

${
  $d G M r $.

  q2275191-simple-integral-definition $a |- (
    Q2275191SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q2275191-lintegral-definition $a |- (
    Q2275191LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q2275191Simple M G )
            /\
            (
              A. x e. U. dom M
                ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q2275191SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d A H M x $.

  q2275191-set-lintegral-definition $a |- (
    Q2275191SetLIntegral M H A
  ) =
    (
      Q2275191LIntegral
      M
      (
        x e. U. dom M |->
          if ( x e. A , ( H ` x ) , 0 )
      )
    )
  $.
$}

${
  $d G H M N x $.

  q2275191-aemeasurable-definition $a |- (
    ( Q2275191AEMeasurable M H )
    <->
    (
      H : U. dom M --> ( 0 [,] +oo )
      /\
      E. G
        (
          G e.
            (
              dom M
              MblFnM
              (
                sigaGen `
                ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
              )
            )
          /\
          E. N e. dom M
            (
              ( M ` N ) = 0
              /\
              A. x e. ( U. dom M \ N )
                ( H ` x ) = ( G ` x )
            )
        )
    )
  ) $.
$}

${
  $d A B $.

  q2275191-ediv-definition $a |- (
    Q2275191EDiv A B
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
  $d A D H J M U V X e x z $.

  q2275191-tendsto-at-definition $a |- (
    ( Q2275191TendstoAt M D V H x z )
    <->
    (
      H : ~P ( U. dom M ) --> ( 0 [,] +oo )
      /\
      A. U e.
        ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
        (
          z e. U
          ->
          E. e e. RR
            (
              0 < e
              /\
              A. A e. ( V ` x )
                (
                  A C_ (
                    Q2275191ClosedBall D ( U. dom M ) x e
                  )
                  ->
                  ( H ` A ) e. U
                )
            )
        )
    )
  ) $.
$}

${
  $d A D F G H J M N T U V X e f p q s x y z $.

  thousand-theorems-q2275191-lebesgue-differentiation-theorem $a |-
    A. M e. U. ran measures
      A. D
        A. V e.
          ( ( ~P ( ~P ( U. dom M ) ) ) ^m ( U. dom M ) )
          A. F e. ( ( 0 [,] +oo ) ^m ( U. dom M ) )
            (
              (
                (
                  ( Q2275191PseudoMetric D ( U. dom M ) )
                  /\
                  (
                    ( topGen ` ran ( ball ` D ) ) e. 2ndc
                    /\
                    dom M =
                      ( sigaGen ` ( topGen ` ran ( ball ` D ) ) )
                  )
                )
                /\
                (
                  ( Q2275191LocallyFinite M
                      ( topGen ` ran ( ball ` D ) ) )
                  /\
                  (
                    ( Q2275191VitaliFamily M D V )
                    /\
                    (
                      ( Q2275191AEMeasurable M F )
                      /\
                      ( Q2275191LIntegral M F ) =/= +oo
                    )
                  )
                )
              )
              ->
              E. N e. dom M
                (
                  ( M ` N ) = 0
                  /\
                  A. x e. ( U. dom M \ N )
                    (
                      Q2275191TendstoAt
                      M
                      D
                      V
                      (
                        A e. ~P ( U. dom M ) |->
                          (
                            Q2275191EDiv
                            ( Q2275191SetLIntegral M F A )
                            ( Q2275191Measure M A )
                          )
                      )
                      x
                      ( F ` x )
                    )
                )
            )
  $.
$}
