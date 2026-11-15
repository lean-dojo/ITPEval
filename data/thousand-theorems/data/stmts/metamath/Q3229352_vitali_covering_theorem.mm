$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3229352
  (thousand-theorems__metamath__Q3229352), "Vitali covering theorem": a fine
  family of closed sets satisfying a uniform measure comparison in a
  second-countable locally finite pseudometric measure space, with topology
  generated directly by its pseudometric balls, has a countable pairwise-
  disjoint subfamily covering the given set almost everywhere. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q3229352PseudoMetric restricts SetMM's extended pseudometrics to finite real
  distances, matching Lean's PseudoMetricSpace. Q3229352ClosedBall is the
  corresponding closed ball. Q3229352Measure evaluates the outer measure
  induced by a measure, so it applies to arbitrary sets just as Lean's Measure
  does. Q3229352LocallyFinite states that every point has an open neighborhood
  of finite measure. Every topological notion below uses the pseudometric
  topology ( topGen ` ran ( ball ` D ) ) generated directly by its balls.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or bidirectional definitions, and this
  database contains no $p proof statement.
$)

$c Q3229352PseudoMetric Q3229352ClosedBall Q3229352Measure
   Q3229352LocallyFinite $.

q3229352-pseudometric-syntax $a
  wff ( Q3229352PseudoMetric D X ) $.
q3229352-closed-ball-syntax $a
  class ( Q3229352ClosedBall D X x e ) $.
q3229352-measure-syntax $a
  class ( Q3229352Measure M A ) $.
q3229352-locally-finite-syntax $a
  wff ( Q3229352LocallyFinite M J ) $.

${
  $d D X x y $.

  q3229352-pseudometric-definition $a |- (
    ( Q3229352PseudoMetric D X )
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

  q3229352-closed-ball-definition $a |- (
    Q3229352ClosedBall D X x e
  ) =
    { y e. X | ( x D y ) <_ e }
  $.
$}

${
  $d A M $.

  q3229352-measure-definition $a |- (
    Q3229352Measure M A
  ) =
    ( ( toOMeas ` M ) ` A )
  $.
$}

${
  $d J M v x $.

  q3229352-locally-finite-definition $a |- (
    ( Q3229352LocallyFinite M J )
    <->
    A. x e. U. dom M
      E. v e. J
        (
          x e. v
          /\
          ( M ` v ) < +oo
        )
  ) $.
$}

${
  $d a b c d e f i k m r s t u x $.

  thousand-theorems-q3229352-vitali-covering-theorem $a |-
    A. m e. U. ran measures
      A. d A. i A. s A. t A. k A. r A. c A. f
        (
          (
            (
              ( Q3229352PseudoMetric d ( U. dom m ) )
              /\
              (
                ( topGen ` ran ( ball ` d ) ) e. 2ndc
                /\
                ( topGen ` ran ( ball ` d ) ) C_ dom m
              )
            )
            /\
            (
              (
                Q3229352LocallyFinite
                m
                ( topGen ` ran ( ball ` d ) )
              )
              /\
              (
                s C_ U. dom m
                /\
                (
                  t C_ i
                  /\
                  (
                    k e. ( 0 [,) +oo )
                    /\
                    (
                      r e. ( RR ^m i )
                      /\
                      (
                        c e. ( ( U. dom m ) ^m i )
                        /\
                        f e. ( ( ~P ( U. dom m ) ) ^m i )
                      )
                    )
                  )
                )
              )
            )
          )
          ->
          (
            (
              A. a e. t
                ( f ` a ) C_
                  (
                    Q3229352ClosedBall
                    d
                    ( U. dom m )
                    ( c ` a )
                    ( r ` a )
                  )
              /\
              (
                A. a e. t
                  (
                    Q3229352Measure
                    m
                    (
                      Q3229352ClosedBall
                      d
                      ( U. dom m )
                      ( c ` a )
                      ( 3 x. ( r ` a ) )
                    )
                  )
                  <_
                  (
                    k
                    *e
                    ( Q3229352Measure m ( f ` a ) )
                  )
                /\
                (
                  A. a e. t
                    (
                      (
                        (
                          int
                          ` ( topGen ` ran ( ball ` d ) )
                        )
                        ` ( f ` a )
                      )
                      =/=
                      (/)
                    )
                  /\
                  (
                    A. a e. t
                      ( f ` a ) e.
                        (
                          Clsd
                          ` ( topGen ` ran ( ball ` d ) )
                        )
                    /\
                    A. x e. s A. e e. RR
                      (
                        0 < e
                        ->
                        E. a e. t
                          (
                            ( r ` a ) <_ e
                            /\
                            ( c ` a ) = x
                          )
                      )
                  )
                )
              )
            )
            ->
            E. u
              (
                u C_ t
                /\
                (
                  u ~<_ NN0
                  /\
                  (
                    A. a e. u A. b e. u
                      (
                        a =/= b
                        ->
                        ( ( f ` a ) i^i ( f ` b ) ) = (/)
                      )
                    /\
                    (
                      Q3229352Measure
                      m
                      (
                        s
                        \
                        U_ a e. u ( f ` a )
                      )
                    ) = 0
                  )
                )
              )
          )
        )
  $.
$}
