$(
  Statement-only formalization of Thousand Theorems corpus artifact Q866116
  (thousand-theorems__metamath__Q866116), "Hahn&ndash;Banach theorem": every
  continuous linear functional on a subspace of a seminormed space over a
  real- or complex-like normed field extends to the whole space without
  changing its operator norm. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q866116SeminormedSpace K V states exactly the additive seminorm and scalar
  laws for a seminormed vector space V over K; norm definiteness is not
  required. Q866116ContinuousLinear K V T says that T is a K-linear
  functional with a finite global seminorm bound, which is equivalent to
  continuity over the nontrivially normed fields RRfld and CCfld.
  Q866116OperatorNorm K V T is the infimum of all nonnegative global bounds,
  hence the usual operator norm of T.

  Mathlib's IsRCLikeNormedField parameter is represented by SetMM's canonical
  real and complex normed fields RRfld and CCfld. Every such mathlib field is
  isometrically isomorphic to one of these two canonical fields, and transport
  of the scalar field, vector space, subspace, and functional across that
  isomorphism preserves extension, restriction, and operator norm; conversely
  RRfld and CCfld instantiate the source field class.

  For p in LSubSp(V), V |`s p is the inherited vector-space structure on p.
  The final assertion retains the arbitrary space, subspace, and functional,
  and keeps the extending functional g internally existentially quantified.
  It is the single unproved corpus $a statement. All preceding $a
  declarations are syntax or faithful definitions, and this database contains
  no $p proof statement.
$)

$c Q866116SeminormedSpace Q866116ContinuousLinear Q866116OperatorNorm $.

q866116-seminormed-space-syntax
  $a wff ( Q866116SeminormedSpace K V ) $.
q866116-continuous-linear-syntax
  $a wff ( Q866116ContinuousLinear K V T ) $.
q866116-operator-norm-syntax
  $a class ( Q866116OperatorNorm K V T ) $.

${
  $d K V a x y $.

  q866116-seminormed-space-definition $a |- (
    ( Q866116SeminormedSpace K V )
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
  $d C K T V x $.

  q866116-continuous-linear-definition $a |- (
    ( Q866116ContinuousLinear K V T )
    <->
    (
      T e. ( V LMHom ( ringLMod ` K ) )
      /\
      E. C e. RR
        (
          0 <_ C
          /\
          A. x e. ( Base ` V )
            (
              ( norm ` K )
              `
              ( T ` x )
            )
            <_
            (
              C
              x.
              ( ( norm ` V ) ` x )
            )
        )
    )
  ) $.
$}

${
  $d C K T V x $.

  q866116-operator-norm-definition $a |- (
    Q866116OperatorNorm K V T
  ) = inf (
    {
      C e. RR |
      (
        0 <_ C
        /\
        A. x e. ( Base ` V )
          (
            ( norm ` K )
            `
            ( T ` x )
          )
          <_
          (
            C
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
  $d K V f g p x $.

  thousand-theorems-q866116-hahn-banach $a |-
    A. K e. { RRfld , CCfld }
      A. V
        (
          ( Q866116SeminormedSpace K V )
          ->
          A. p e. ( LSubSp ` V )
            A. f
              (
                ( Q866116ContinuousLinear K ( V |`s p ) f )
                ->
                E. g
                  (
                    ( Q866116ContinuousLinear K V g )
                    /\
                    A. x e. p
                      ( g ` x ) = ( f ` x )
                    /\
                    (
                      Q866116OperatorNorm K V g
                    )
                    =
                    (
                      Q866116OperatorNorm K ( V |`s p ) f
                    )
                  )
              )
        )
  $.
$}
