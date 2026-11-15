$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1426292
  (thousand-theorems__metamath__Q1426292), "Banach&ndash;Steinhaus theorem": an
  arbitrary pointwise bounded family of continuous semilinear maps from a
  complete seminormed space to a seminormed space has uniformly bounded
  operator norms. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1426292SeminormedSpace K V says that V is a SetMM vector space over the
  normed field K equipped with a nonnegative seminorm satisfying the triangle
  inequality and the normed-space scalar law. Definiteness is deliberately
  not required, matching Lean's SeminormedAddCommGroup rather than the
  stronger SetMM NrmVec class.

  Q1426292Complete V is Cauchy-sequence completeness for the pseudometric
  induced by V's seminorm. For seminormed additive groups this is equivalent
  to Lean's CompleteSpace filter formulation.

  Q1426292IsometricRingHom K L S states that S is a ring homomorphism from K
  to L preserving norms. Q1426292ContinuousSemilinear K L S V W T states
  that T is additive, S-semilinear, and has a finite global seminorm bound;
  the latter is equivalent to continuity for semilinear maps over a
  nontrivially normed field. Q1426292OperatorNorm V W T is the infimum of all
  nonnegative global bounds, exactly the operator norm of T.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q1426292Sub Q1426292SeminormedSpace Q1426292Complete
   Q1426292IsometricRingHom Q1426292ContinuousSemilinear
   Q1426292OperatorNorm Q1426292Family $.

q1426292-sub-syntax $a class ( Q1426292Sub V x y ) $.
q1426292-seminormed-space-syntax
  $a wff ( Q1426292SeminormedSpace K V ) $.
q1426292-complete-syntax $a wff ( Q1426292Complete V ) $.
q1426292-isometric-ring-hom-syntax
  $a wff ( Q1426292IsometricRingHom K L S ) $.
q1426292-continuous-semilinear-syntax
  $a wff ( Q1426292ContinuousSemilinear K L S V W T ) $.
q1426292-operator-norm-syntax
  $a class ( Q1426292OperatorNorm V W T ) $.
q1426292-family-syntax
  $a wff ( Q1426292Family K L S V W I G ) $.

${
  $d V x y $.

  q1426292-sub-definition $a |- (
    Q1426292Sub V x y
  ) = (
    x
    ( +g ` V )
    ( ( -g ` V ) ` y )
  ) $.
$}

${
  $d K V a x y $.

  q1426292-seminormed-space-definition $a |- (
    ( Q1426292SeminormedSpace K V )
    <->
    (
      V e. LVec
      /\
      ( Scalar ` V ) = K
      /\
      ( norm ` V ) : ( Base ` V ) --> RR
      /\
      ( ( norm ` V ) ` ( 0g ` V ) ) = 0
      /\
      A. x e. ( Base ` V )
        0 <_ ( ( norm ` V ) ` x )
      /\
      A. x e. ( Base ` V )
        A. y e. ( Base ` V )
          (
            ( norm ` V )
            `
            ( x ( +g ` V ) y )
          )
          <_
          (
            ( ( norm ` V ) ` x )
            +
            ( ( norm ` V ) ` y )
          )
      /\
      A. a e. ( Base ` K )
        A. x e. ( Base ` V )
          (
            ( norm ` V )
            `
            ( a ( .s ` V ) x )
          )
          =
          (
            ( ( norm ` K ) ` a )
            x.
            ( ( norm ` V ) ` x )
          )
    )
  ) $.
$}

${
  $d V e h k m n x $.

  q1426292-complete-definition $a |- (
    ( Q1426292Complete V )
    <->
    A. h e. ( ( Base ` V ) ^m NN0 )
      (
        (
          A. e e. RR+
            E. k e. NN0
              A. m e. ( ZZ>= ` k )
                A. n e. ( ZZ>= ` k )
                  (
                    ( norm ` V )
                    `
                    (
                      Q1426292Sub V
                        ( h ` m )
                        ( h ` n )
                    )
                  )
                  <
                  e
        )
        ->
        E. x e. ( Base ` V )
          A. e e. RR+
            E. k e. NN0
              A. m e. ( ZZ>= ` k )
                (
                  ( norm ` V )
                  `
                  (
                    Q1426292Sub V
                      ( h ` m )
                      x
                  )
                )
                <
                e
      )
  ) $.
$}

${
  $d K L S a $.

  q1426292-isometric-ring-hom-definition $a |- (
    ( Q1426292IsometricRingHom K L S )
    <->
    (
      S e. ( K RingHom L )
      /\
      A. a e. ( Base ` K )
        (
          ( norm ` L )
          `
          ( S ` a )
        )
        =
        ( ( norm ` K ) ` a )
    )
  ) $.
$}

${
  $d K L S T V W a b x $.

  q1426292-continuous-semilinear-definition $a |- (
    ( Q1426292ContinuousSemilinear K L S V W T )
    <->
    (
      T e. ( V GrpHom W )
      /\
      A. a e. ( Base ` K )
        A. x e. ( Base ` V )
          (
            T
            `
            ( a ( .s ` V ) x )
          )
          =
          (
            ( S ` a )
            ( .s ` W )
            ( T ` x )
          )
      /\
      E. b e. RR
        (
          0 <_ b
          /\
          A. x e. ( Base ` V )
            (
              ( norm ` W )
              `
              ( T ` x )
            )
            <_
            (
              b
              x.
              ( ( norm ` V ) ` x )
            )
        )
    )
  ) $.
$}

${
  $d T V W c x $.

  q1426292-operator-norm-definition $a |- (
    Q1426292OperatorNorm V W T
  ) = inf (
    {
      c e. RR |
      (
        0 <_ c
        /\
        A. x e. ( Base ` V )
          (
            ( norm ` W )
            `
            ( T ` x )
          )
          <_
          (
            c
            x.
            ( ( norm ` V ) ` x )
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
  $d G I K L S T V W $.

  q1426292-family-definition $a |- (
    ( Q1426292Family K L S V W I G )
    <->
    G : I --> {
      T |
      ( Q1426292ContinuousSemilinear K L S V W T )
    }
  ) $.
$}

${
  $d b c d g i j k l s v w x $.

  thousand-theorems-q1426292-banach-steinhaus $a |-
    A. k e. ( NrmRing i^i Field )
      A. l e. ( NrmRing i^i Field )
        A. v
          A. w
            A. s
              A. j
                A. g
                  (
                    (
                      E. c e. ( Base ` k )
                        1 < ( ( norm ` k ) ` c )
                      /\
                      E. c e. ( Base ` l )
                        1 < ( ( norm ` l ) ` c )
                      /\
                      ( Q1426292SeminormedSpace k v )
                      /\
                      ( Q1426292SeminormedSpace l w )
                      /\
                      ( Q1426292Complete v )
                      /\
                      ( Q1426292IsometricRingHom k l s )
                      /\
                      ( Q1426292Family k l s v w j g )
                    )
                    ->
                    (
                      (
                        A. x e. ( Base ` v )
                          E. b e. RR
                            A. i e. j
                              (
                                ( norm ` w )
                                `
                                ( ( g ` i ) ` x )
                              )
                              <_
                              b
                      )
                      ->
                      E. d e. RR
                        A. i e. j
                          (
                            Q1426292OperatorNorm
                              v
                              w
                              ( g ` i )
                          )
                          <_
                          d
                    )
                  )
  $.
$}
