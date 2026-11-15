$(
  Statement-only formalization of Thousand Theorems corpus artifact Q530152
  (thousand-theorems__metamath__Q530152), "Picard&ndash;Lindel&ouml;f theorem":
  a time-dependent vector field on an arbitrary real Banach space satisfying
  the local Lipschitz, continuity, norm-bound, and interval-size hypotheses
  has a local solution through every permitted initial point. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  V ranges over SetMM normed vector spaces over RRfld, and V e. CMetSp is
  completeness for the norm metric. F is a time-dependent vector field,
  represented as a function from RR to the full function space Base(V) ^
  Base(V). Q530152ClosedBall is the norm-closed ball.

  Q530152ContinuousOn is relative epsilon-delta continuity.
  Q530152LipschitzOn is the source LipschitzOnWith predicate.
  Q530152HasDerivWithin is the epsilon-delta remainder characterization of
  HasDerivWithinAt for a curve RR -> Base(V), including its one-sided
  interpretation at interval endpoints. Q530152IsPicardLindelof expands all
  four fields of the source structure. The final declaration is the single
  unproved corpus $a statement; all preceding $a declarations are syntax or
  explicit bidirectional definitions.
$)

$c Q530152Sub Q530152Max Q530152ClosedBall Q530152ContinuousOn
   Q530152LipschitzOn Q530152HasDerivWithin
   Q530152IsPicardLindelof $.

q530152-sub-syntax $a class ( Q530152Sub V x y ) $.
q530152-max-syntax $a class ( Q530152Max A B ) $.
q530152-closed-ball-syntax
  $a class ( Q530152ClosedBall V X A ) $.
q530152-continuous-on-syntax
  $a wff ( Q530152ContinuousOn V G S ) $.
q530152-lipschitz-on-syntax
  $a wff ( Q530152LipschitzOn V K G S ) $.
q530152-has-deriv-within-syntax
  $a wff ( Q530152HasDerivWithin V H C S T ) $.
q530152-is-picard-lindelof-syntax
  $a wff
    ( Q530152IsPicardLindelof V F M N T X A R L K ) $.

${
  $d V x y $.

  q530152-sub-definition $a |- (
    Q530152Sub V x y
  ) = (
    x
    ( +g ` V )
    ( ( -g ` V ) ` y )
  ) $.
$}

${
  $d A B $.

  q530152-max-definition $a |- (
    Q530152Max A B
  ) = if ( A <_ B , B , A ) $.
$}

${
  $d A V X y $.

  q530152-closed-ball-definition $a |- (
    Q530152ClosedBall V X A
  ) = {
    y e. ( Base ` V ) |
      (
        ( norm ` V )
        `
        ( Q530152Sub V y X )
      )
      <_
      A
  } $.
$}

${
  $d G S V d e x y $.

  q530152-continuous-on-definition $a |- (
    ( Q530152ContinuousOn V G S )
    <->
    A. x e. S
      A. e e. RR+
        E. d e. RR+
          A. y e. S
            (
              ( ( abs ` ( y - x ) ) < d )
              ->
              (
                ( norm ` V )
                `
                (
                  Q530152Sub
                  V
                  ( G ` y )
                  ( G ` x )
                )
              )
              <
              e
            )
  ) $.
$}

${
  $d G K S V x y $.

  q530152-lipschitz-on-definition $a |- (
    ( Q530152LipschitzOn V K G S )
    <->
    A. x e. S
      A. y e. S
        (
          ( norm ` V )
          `
          (
            Q530152Sub
            V
            ( G ` x )
            ( G ` y )
          )
        )
        <_
        (
          K
          x.
          (
            ( norm ` V )
            `
            ( Q530152Sub V x y )
          )
        )
  ) $.
$}

${
  $d C H S T V d e y $.

  q530152-has-deriv-within-definition $a |- (
    ( Q530152HasDerivWithin V H C S T )
    <->
    A. e e. RR+
      E. d e. RR+
        A. y e. S
          (
            ( ( abs ` ( y - T ) ) < d )
            ->
            (
              ( norm ` V )
              `
              (
                Q530152Sub
                V
                (
                  Q530152Sub
                  V
                  ( H ` y )
                  ( H ` T )
                )
                (
                  ( y - T )
                  ( .s ` V )
                  C
                )
              )
            )
            <_
            (
              e
              x.
              ( abs ` ( y - T ) )
            )
          )
  ) $.
$}

${
  $d A F K L M N R T V X t x $.

  q530152-is-picard-lindelof-definition $a |- (
    (
      Q530152IsPicardLindelof
      V F M N T X A R L K
    )
    <->
    (
      A. t e. ( M [,] N )
        (
          Q530152LipschitzOn
          V
          K
          ( F ` t )
          ( Q530152ClosedBall V X A )
        )
      /\
      A. x e. ( Q530152ClosedBall V X A )
        (
          Q530152ContinuousOn
          V
          ( t e. RR |-> ( ( F ` t ) ` x ) )
          ( M [,] N )
        )
      /\
      A. t e. ( M [,] N )
        A. x e. ( Q530152ClosedBall V X A )
          (
            ( ( norm ` V ) ` ( ( F ` t ) ` x ) )
            <_
            L
          )
      /\
      (
        L
        x.
        (
          Q530152Max
          ( N - T )
          ( T - M )
        )
      )
      <_
      ( A - R )
    )
  ) $.
$}

${
  $d A F H K L M N R T V X Y t w $.

  thousand-theorems-q530152-picard-lindelof $a |-
    A. V e. { w e. NrmVec | ( Scalar ` w ) = RRfld }
      A. F A. M A. N A. T A. X A. A A. R A. L A. K A. Y
        (
          (
            V e. CMetSp
            /\
            F e.
              (
                ( ( Base ` V ) ^m ( Base ` V ) )
                ^m
                RR
              )
            /\
            ( M e. RR /\ N e. RR )
            /\
            T e. ( M [,] N )
            /\
            X e. ( Base ` V )
            /\
            Y e. ( Base ` V )
            /\
            A e. ( 0 [,) +oo )
            /\
            R e. ( 0 [,) +oo )
            /\
            L e. ( 0 [,) +oo )
            /\
            K e. ( 0 [,) +oo )
          )
          ->
          (
            (
              (
                Q530152IsPicardLindelof
                V F M N T X A R L K
              )
              /\
              Y e. ( Q530152ClosedBall V X R )
            )
            ->
            E. H e. ( ( Base ` V ) ^m RR )
              (
                ( H ` T ) = Y
                /\
                A. t e. ( M [,] N )
                  (
                    Q530152HasDerivWithin
                    V
                    H
                    ( ( F ` t ) ` ( H ` t ) )
                    ( M [,] N )
                    t
                  )
              )
          )
        )
  $.
$}
