$(
  Statement-only formalization of Thousand Theorems corpus artifact Q537618
  (thousand-theorems__metamath__Q537618), "Banach-Alaoglu theorem": over an
  arbitrary proper nontrivially normed field, the polar of a neighborhood of
  zero in a seminormed vector space is compact in the weak-star topology of
  the continuous dual. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q537618SeminormedSpace K V gives the exact seminorm and scalar laws of a
  seminormed vector space V over K, without adding norm definiteness.
  Q537618ContinuousLinear K V T says that T is a K-linear functional with a
  global seminorm bound, equivalently a continuous linear functional.

  Q537618WeakTopology K V is the subspace topology on the continuous dual
  inherited from the product of copies of K indexed by Base(V), hence exactly
  the topology of pointwise convergence. Q537618NeighborhoodZero V S says
  that S contains a positive-radius seminorm ball about zero, equivalent to
  membership in the neighborhood filter at zero. Q537618Proper K requires
  every norm-closed ball in K to be compact. Q537618Polar K V S is the set of
  continuous linear functionals whose norm is at most one on S.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q537618Sub Q537618SeminormedSpace Q537618Proper
   Q537618ContinuousLinear Q537618Dual Q537618WeakTopology
   Q537618NeighborhoodZero Q537618Polar $.

q537618-sub-syntax
  $a class ( Q537618Sub V x y ) $.
q537618-seminormed-space-syntax
  $a wff ( Q537618SeminormedSpace K V ) $.
q537618-proper-syntax
  $a wff ( Q537618Proper K ) $.
q537618-continuous-linear-syntax
  $a wff ( Q537618ContinuousLinear K V T ) $.
q537618-dual-syntax
  $a class ( Q537618Dual K V ) $.
q537618-weak-topology-syntax
  $a class ( Q537618WeakTopology K V ) $.
q537618-neighborhood-zero-syntax
  $a wff ( Q537618NeighborhoodZero V S ) $.
q537618-polar-syntax
  $a class ( Q537618Polar K V S ) $.

${
  $d V x y $.

  q537618-sub-definition $a |- (
    Q537618Sub V x y
  ) = (
    x
    ( +g ` V )
    ( ( -g ` V ) ` y )
  ) $.
$}

${
  $d K V a x y $.

  q537618-seminormed-space-definition $a |- (
    ( Q537618SeminormedSpace K V )
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
  $d K p r y $.

  q537618-proper-definition $a |- (
    ( Q537618Proper K )
    <->
    A. p e. ( Base ` K )
      A. r e. RR
        (
          ( TopOpen ` K )
          |`t
          {
            y e. ( Base ` K ) |
            (
              ( norm ` K )
              `
              ( Q537618Sub K y p )
            )
            <_
            r
          }
        ) e. Comp
  ) $.
$}

${
  $d C K T V x $.

  q537618-continuous-linear-definition $a |- (
    ( Q537618ContinuousLinear K V T )
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
  $d K T V $.

  q537618-dual-definition $a |- (
    Q537618Dual K V
  ) = {
    T |
    ( Q537618ContinuousLinear K V T )
  } $.
$}

${
  $d K V $.

  q537618-weak-topology-definition $a |- (
    Q537618WeakTopology K V
  ) = (
    (
      Xt_
      `
      (
        ( Base ` V )
        X.
        { ( TopOpen ` K ) }
      )
    )
    |`t
    ( Q537618Dual K V )
  ) $.
$}

${
  $d S V e x $.

  q537618-neighborhood-zero-definition $a |- (
    ( Q537618NeighborhoodZero V S )
    <->
    E. e e. RR+
      A. x e. ( Base ` V )
        (
          (
            ( norm ` V )
            `
            x
          )
          <
          e
          ->
          x e. S
        )
  ) $.
$}

${
  $d K S T V x $.

  q537618-polar-definition $a |- (
    Q537618Polar K V S
  ) = {
    T e. ( Q537618Dual K V ) |
    A. x e. S
      (
        ( norm ` K )
        `
        ( T ` x )
      )
      <_
      1
  } $.
$}

${
  $d K S V c $.

  thousand-theorems-q537618-banach-alaoglu $a |-
    A. K e. ( NrmRing i^i Field )
      A. V
        A. S
          (
            (
              E. c e. ( Base ` K )
                1 < ( ( norm ` K ) ` c )
              /\
              ( Q537618SeminormedSpace K V )
              /\
              ( Q537618Proper K )
              /\
              S C_ ( Base ` V )
              /\
              ( Q537618NeighborhoodZero V S )
            )
            ->
            (
              ( Q537618WeakTopology K V )
              |`t
              ( Q537618Polar K V S )
            ) e. Comp
          )
  $.
$}
