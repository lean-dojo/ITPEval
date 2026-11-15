$(
  Statement-only formalization of Thousand Theorems corpus artifact Q944297
  (thousand-theorems__metamath__Q944297),
  "Open mapping theorem (functional analysis)": a surjective continuous
  semilinear map between complete normed vector spaces over isometrically
  inverse nontrivially normed fields is an open map. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NrmVec class supplies the additive group, scalar action, norm,
  norm-induced metric, and norm topology of a normed vector space. Membership
  in CMetSp is completeness for that metric.

  Q944297IsometricInvPair K L S R expands the two isometric ring
  homomorphisms and both inverse identities of Lean's RingHomInvPair S R,
  RingHomIsometric S, and RingHomIsometric R assumptions.
  Q944297ContinuousSemilinear K L S V W T says that T is additive,
  S-semilinear, and continuous for the two norm topologies.
  Q944297Surjective and Q944297OpenMap are the direct set-theoretic
  renderings of Function.Surjective and IsOpenMap.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q944297IsometricInvPair Q944297ContinuousSemilinear
   Q944297Surjective Q944297OpenMap $.

q944297-isometric-inv-pair-syntax
  $a wff ( Q944297IsometricInvPair K L S R ) $.
q944297-continuous-semilinear-syntax
  $a wff ( Q944297ContinuousSemilinear K L S V W T ) $.
q944297-surjective-syntax
  $a wff ( Q944297Surjective V W T ) $.
q944297-open-map-syntax
  $a wff ( Q944297OpenMap V W T ) $.

${
  $d K L R S a b $.

  q944297-isometric-inv-pair-definition $a |- (
    ( Q944297IsometricInvPair K L S R )
    <->
    (
      S e. ( K RingHom L )
      /\
      R e. ( L RingHom K )
      /\
      A. a e. ( Base ` K )
        ( R ` ( S ` a ) ) = a
      /\
      A. b e. ( Base ` L )
        ( S ` ( R ` b ) ) = b
      /\
      A. a e. ( Base ` K )
        (
          ( norm ` L )
          `
          ( S ` a )
        )
        =
        ( ( norm ` K ) ` a )
      /\
      A. b e. ( Base ` L )
        (
          ( norm ` K )
          `
          ( R ` b )
        )
        =
        ( ( norm ` L ) ` b )
    )
  ) $.
$}

${
  $d K L S T V W a x $.

  q944297-continuous-semilinear-definition $a |- (
    ( Q944297ContinuousSemilinear K L S V W T )
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
      T e. (
        ( TopOpen ` V )
        Cn
        ( TopOpen ` W )
      )
    )
  ) $.
$}

${
  $d T V W x y $.

  q944297-surjective-definition $a |- (
    ( Q944297Surjective V W T )
    <->
    A. y e. ( Base ` W )
      E. x e. ( Base ` V )
        ( T ` x ) = y
  ) $.
$}

${
  $d O T V W $.

  q944297-open-map-definition $a |- (
    ( Q944297OpenMap V W T )
    <->
    A. O e. ( TopOpen ` V )
      ( T " O ) e. ( TopOpen ` W )
  ) $.
$}

${
  $d K L R S T V W c v w $.

  thousand-theorems-q944297-open-mapping-theorem $a |-
    A. K e. ( NrmRing i^i Field )
      A. L e. ( NrmRing i^i Field )
        A. V e. { v e. NrmVec | ( Scalar ` v ) = K }
          A. W e. { w e. NrmVec | ( Scalar ` w ) = L }
            A. S
              A. R
                A. T
                  (
                    (
                      E. c e. ( Base ` K )
                        1 < ( ( norm ` K ) ` c )
                      /\
                      E. c e. ( Base ` L )
                        1 < ( ( norm ` L ) ` c )
                      /\
                      V e. CMetSp
                      /\
                      W e. CMetSp
                      /\
                      ( Q944297IsometricInvPair K L S R )
                      /\
                      ( Q944297ContinuousSemilinear K L S V W T )
                    )
                    ->
                    (
                      ( Q944297Surjective V W T )
                      ->
                      ( Q944297OpenMap V W T )
                    )
                  )
  $.
$}
