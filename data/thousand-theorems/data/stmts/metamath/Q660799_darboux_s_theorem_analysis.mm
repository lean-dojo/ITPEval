$(
  Statement-only formalization of Thousand Theorems corpus artifact Q660799
  (thousand-theorems__metamath__Q660799), "Darboux's theorem (analysis)":
  derivatives of real functions have the intermediate value property on
  intervals, equivalently their images on order-connected or convex real sets
  are order-connected or convex. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q660799HasDerivWithin is the real epsilon-delta remainder formulation of
  HasDerivWithinAt. Q660799DifferentiableOn existentially quantifies the
  within-set derivative at each point.

  Q660799DerivWithin totalizes the unique within-set derivative, returning
  zero when it is absent or nonunique. On a real order-connected set with at
  least two points, every within derivative is unique; on an empty or singleton
  set, every derivative image is empty or a singleton. Thus this canonical
  totalization is bidirectionally equivalent to Mathlib's choice-based
  derivWithin for each image-connectedness assertion below. Q660799Deriv is
  the corresponding totalized ordinary derivative on RR.

  Q660799OrdConnected and Q660799Convex are the standard real definitions.
  The image operators retain existentially quantified preimages. The ten final
  $a declarations are the indexed unproved corpus statements. The last one
  follows its formal Lean signature, which duplicates the preceding closed-
  interval endpoint inequalities.
$)

$c Q660799HasDerivWithin Q660799DifferentiableOn
   Q660799DerivWithin Q660799Deriv Q660799OrdConnected Q660799Convex
   Q660799Image Q660799DerivWithinImage Q660799DerivImage $.

q660799-has-deriv-within-syntax
  $a wff ( Q660799HasDerivWithin F G S X ) $.
q660799-differentiable-on-syntax
  $a wff ( Q660799DifferentiableOn F S ) $.
q660799-deriv-within-syntax
  $a class ( Q660799DerivWithin F S X ) $.
q660799-deriv-syntax
  $a class ( Q660799Deriv F X ) $.
q660799-ord-connected-syntax
  $a wff ( Q660799OrdConnected S ) $.
q660799-convex-syntax
  $a wff ( Q660799Convex S ) $.
q660799-image-syntax
  $a class ( Q660799Image F S ) $.
q660799-deriv-within-image-syntax
  $a class ( Q660799DerivWithinImage F S ) $.
q660799-deriv-image-syntax
  $a class ( Q660799DerivImage F S ) $.

${
  $d F G S X e d y $.

  q660799-has-deriv-within-definition $a |- (
    ( Q660799HasDerivWithin F G S X )
    <->
    (
      (
        F e. ( RR ^m RR )
        /\
        (
          G e. RR
          /\
          (
            S C_ RR
            /\
            X e. RR
          )
        )
      )
      /\
      A. e e. RR+
        E. d e. RR+
          A. y e. S
            (
              ( ( abs ` ( y - X ) ) < d )
              ->
              (
                (
                  abs
                  `
                  (
                    ( ( F ` y ) - ( F ` X ) )
                    -
                    ( G x. ( y - X ) )
                  )
                )
                <_
                ( e x. ( abs ` ( y - X ) ) )
              )
            )
    )
  ) $.
$}

${
  $d F S X G $.

  q660799-differentiable-on-definition $a |- (
    ( Q660799DifferentiableOn F S )
    <->
    (
      (
        F e. ( RR ^m RR )
        /\
        S C_ RR
      )
      /\
      A. X e. S
        E. G e. RR
          ( Q660799HasDerivWithin F G S X )
    )
  ) $.
$}

${
  $d F S X G $.

  q660799-deriv-within-definition $a |- (
    Q660799DerivWithin F S X
  ) =
    if
    (
      E! G e. RR
        ( Q660799HasDerivWithin F G S X ) ,
      (
        iota_ G e. RR
          ( Q660799HasDerivWithin F G S X )
      ) ,
      0
    )
  $.
$}

${
  $d F X G $.

  q660799-deriv-definition $a |- (
    Q660799Deriv F X
  ) =
    if
    (
      E! G e. RR
        ( Q660799HasDerivWithin F G RR X ) ,
      (
        iota_ G e. RR
          ( Q660799HasDerivWithin F G RR X )
      ) ,
      0
    )
  $.
$}

${
  $d S a b x $.

  q660799-ord-connected-definition $a |- (
    ( Q660799OrdConnected S )
    <->
    (
      S C_ RR
      /\
      A. a e. S A. b e. S A. x e. RR
        (
          (
            (
              a <_ x
              /\
              x <_ b
            )
            \/
            (
              b <_ x
              /\
              x <_ a
            )
          )
          ->
          x e. S
        )
    )
  ) $.
$}

${
  $d S t x y $.

  q660799-convex-definition $a |- (
    ( Q660799Convex S )
    <->
    (
      S C_ RR
      /\
      A. x e. S A. y e. S A. t e. ( 0 [,] 1 )
        (
          (
            ( t x. x )
            +
            ( ( 1 - t ) x. y )
          )
          e. S
        )
    )
  ) $.
$}

${
  $d F S x y $.

  q660799-image-definition $a |- (
    Q660799Image F S
  ) = {
    y e. RR |
      E. x e. S
        ( F ` x ) = y
  } $.
$}

${
  $d F S x y $.

  q660799-deriv-within-image-definition $a |- (
    Q660799DerivWithinImage F S
  ) = {
    y e. RR |
      E. x e. S
        ( Q660799DerivWithin F S x ) = y
  } $.
$}

${
  $d F S x y $.

  q660799-deriv-image-definition $a |- (
    Q660799DerivImage F S
  ) = {
    y e. RR |
      E. x e. S
        ( Q660799Deriv F x ) = y
  } $.
$}

${
  $d A B C F G M X $.

  thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-gt-of-lt
    $a |-
    A. A e. RR A. B e. RR
      A. F e. ( RR ^m RR )
        A. G e. ( RR ^m RR )
          A. M e. RR
            (
              (
                (
                  A <_ B
                  /\
                  A. X e. ( A [,] B )
                    (
                      Q660799HasDerivWithin
                      F
                      ( G ` X )
                      ( A [,] B )
                      X
                    )
                )
                /\
                (
                  ( G ` A ) < M
                  /\
                  M < ( G ` B )
                )
              )
              ->
              E. C e. ( A (,) B )
                ( G ` C ) = M
            )
  $.
$}

${
  $d A B C F G M X $.

  thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-lt-of-gt
    $a |-
    A. A e. RR A. B e. RR
      A. F e. ( RR ^m RR )
        A. G e. ( RR ^m RR )
          A. M e. RR
            (
              (
                (
                  A <_ B
                  /\
                  A. X e. ( A [,] B )
                    (
                      Q660799HasDerivWithin
                      F
                      ( G ` X )
                      ( A [,] B )
                      X
                    )
                )
                /\
                (
                  M < ( G ` A )
                  /\
                  ( G ` B ) < M
                )
              )
              ->
              E. C e. ( A (,) B )
                ( G ` C ) = M
            )
  $.
$}

${
  $d F G S X $.

  thousand-theorems-q660799-ord-connected-image-has-deriv-within-at
    $a |-
    A. F e. ( RR ^m RR )
      A. G e. ( RR ^m RR )
        A. S e. ~P RR
          (
            (
              ( Q660799OrdConnected S )
              /\
              A. X e. S
                (
                  Q660799HasDerivWithin
                  F
                  ( G ` X )
                  S
                  X
                )
            )
            ->
            (
              Q660799OrdConnected
              ( Q660799Image G S )
            )
          )
  $.
$}

${
  $d F S $.

  thousand-theorems-q660799-ord-connected-image-deriv-within
    $a |-
    A. F e. ( RR ^m RR )
      A. S e. ~P RR
        (
          (
            ( Q660799OrdConnected S )
            /\
            ( Q660799DifferentiableOn F S )
          )
          ->
          (
            Q660799OrdConnected
            ( Q660799DerivWithinImage F S )
          )
        )
  $.
$}

${
  $d F G S X $.

  thousand-theorems-q660799-ord-connected-image-deriv
    $a |-
    A. F e. ( RR ^m RR )
      A. S e. ~P RR
        (
          (
            ( Q660799OrdConnected S )
            /\
            A. X e. S
              E. G e. RR
                (
                  Q660799HasDerivWithin
                  F
                  G
                  RR
                  X
                )
          )
          ->
          (
            Q660799OrdConnected
            ( Q660799DerivImage F S )
          )
        )
  $.
$}

${
  $d F G S X $.

  thousand-theorems-q660799-convex-image-has-deriv-within-at
    $a |-
    A. F e. ( RR ^m RR )
      A. G e. ( RR ^m RR )
        A. S e. ~P RR
          (
            (
              ( Q660799Convex S )
              /\
              A. X e. S
                (
                  Q660799HasDerivWithin
                  F
                  ( G ` X )
                  S
                  X
                )
            )
            ->
            (
              Q660799Convex
              ( Q660799Image G S )
            )
          )
  $.
$}

${
  $d F S $.

  thousand-theorems-q660799-convex-image-deriv-within
    $a |-
    A. F e. ( RR ^m RR )
      A. S e. ~P RR
        (
          (
            ( Q660799Convex S )
            /\
            ( Q660799DifferentiableOn F S )
          )
          ->
          (
            Q660799Convex
            ( Q660799DerivWithinImage F S )
          )
        )
  $.
$}

${
  $d F G S X $.

  thousand-theorems-q660799-convex-image-deriv
    $a |-
    A. F e. ( RR ^m RR )
      A. S e. ~P RR
        (
          (
            ( Q660799Convex S )
            /\
            A. X e. S
              E. G e. RR
                (
                  Q660799HasDerivWithin
                  F
                  G
                  RR
                  X
                )
          )
          ->
          (
            Q660799Convex
            ( Q660799DerivImage F S )
          )
        )
  $.
$}

${
  $d A B C F G M X $.

  thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-ge-of-le
    $a |-
    A. A e. RR A. B e. RR
      A. F e. ( RR ^m RR )
        A. G e. ( RR ^m RR )
          A. M e. RR
            (
              (
                (
                  A <_ B
                  /\
                  A. X e. ( A [,] B )
                    (
                      Q660799HasDerivWithin
                      F
                      ( G ` X )
                      ( A [,] B )
                      X
                    )
                )
                /\
                (
                  ( G ` A ) <_ M
                  /\
                  M <_ ( G ` B )
                )
              )
              ->
              E. C e. ( A [,] B )
                ( G ` C ) = M
            )
  $.
$}

${
  $d A B C F G M X $.

  thousand-theorems-q660799-exists-has-deriv-within-at-eq-of-le-of-ge
    $a |-
    A. A e. RR A. B e. RR
      A. F e. ( RR ^m RR )
        A. G e. ( RR ^m RR )
          A. M e. RR
            (
              (
                (
                  A <_ B
                  /\
                  A. X e. ( A [,] B )
                    (
                      Q660799HasDerivWithin
                      F
                      ( G ` X )
                      ( A [,] B )
                      X
                    )
                )
                /\
                (
                  ( G ` A ) <_ M
                  /\
                  M <_ ( G ` B )
                )
              )
              ->
              E. C e. ( A [,] B )
                ( G ` C ) = M
            )
  $.
$}
