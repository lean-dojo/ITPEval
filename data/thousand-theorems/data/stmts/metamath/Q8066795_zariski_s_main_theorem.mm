$(
  Statement-only formalization of Thousand Theorems corpus artifact Q8066795
  (thousand-theorems__metamath__Q8066795), "Zariski's main theorem": a proper
  morphism of schemes whose fiber over a point is finite is finite over some
  open neighborhood of that point. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A scheme X is encoded as a six-entry function. Its entries are respectively
  the point set, topology, rings of sections, restriction homomorphisms,
  point-prime maps on affine opens, and principal-open maps. Q8066795Scheme
  gives the sheaf axioms and an affine-open cover; Q8066795Affine identifies
  every affine open with the prime spectrum of its section ring, including
  the principal-open localization property.

  All stored map families have exact domains: restriction maps are indexed by
  nested open pairs, point-prime and principal-open data by their typed open
  pairs, and morphism section maps by the target topology. A morphism f is a
  five-entry function containing its source, target, continuous point map,
  inverse-image map on opens, and compatible local homomorphisms on sections.
  Properness is expanded as separatedness, universal closedness, and local
  finite type. Pullbacks are characterized by their categorical universal
  property, and finiteness is the affine-local finite-module condition.

  Q8066795FiniteOnOpen f V unfolds finiteness of the canonical restriction of
  f over V: affine opens of the open subscheme V are exactly the affine opens
  of the target contained in V, with the same section rings. Thus the final
  assertion preserves the source's internal existential neighborhood and its
  unrestricted scheme, point, and fiber domains. All declarations below are
  syntax or transparent definitions; the final $a is unproved and there is no
  $p proof statement in this file.
$)

$c Q8066795Localization Q8066795Affine Q8066795Scheme
   Q8066795GermUnit Q8066795Morphism
   Q8066795FiniteModule Q8066795FiniteType
   Q8066795Identity Q8066795Compose Q8066795ClosedMap
   Q8066795ClosedImmersion Q8066795Pullback
   Q8066795Separated Q8066795UniversallyClosed
   Q8066795LocallyFiniteType Q8066795Proper
   Q8066795FiniteOnOpen $.

q8066795-localization-syntax $a wff
  ( Q8066795Localization R S H a ) $.
q8066795-affine-syntax $a wff ( Q8066795Affine X U ) $.
q8066795-scheme-syntax $a wff ( Q8066795Scheme X ) $.
q8066795-germ-unit-syntax $a wff
  ( Q8066795GermUnit X U x a ) $.
q8066795-morphism-syntax $a wff ( Q8066795Morphism f ) $.
q8066795-finite-module-syntax $a wff
  ( Q8066795FiniteModule R S H ) $.
q8066795-finite-type-syntax $a wff
  ( Q8066795FiniteType R S H ) $.
q8066795-identity-syntax $a wff ( Q8066795Identity f X ) $.
q8066795-compose-syntax $a wff ( Q8066795Compose f g h ) $.
q8066795-closed-map-syntax $a wff ( Q8066795ClosedMap f ) $.
q8066795-closed-immersion-syntax $a wff
  ( Q8066795ClosedImmersion f ) $.
q8066795-pullback-syntax $a wff
  ( Q8066795Pullback f g W p q ) $.
q8066795-separated-syntax $a wff ( Q8066795Separated f ) $.
q8066795-universally-closed-syntax $a wff
  ( Q8066795UniversallyClosed f ) $.
q8066795-locally-finite-type-syntax $a wff
  ( Q8066795LocallyFiniteType f ) $.
q8066795-proper-syntax $a wff ( Q8066795Proper f ) $.
q8066795-finite-on-open-syntax $a wff
  ( Q8066795FiniteOnOpen f V ) $.

${
  $d H R S a b c n v $.

  q8066795-localization-definition $a |- (
    Q8066795Localization R S H a
    <->
    (
      R e. CRing
      /\
      S e. CRing
      /\
      H e. ( R RingHom S )
      /\
      a e. ( Base ` R )
      /\
      ( H ` a ) e. ( Unit ` S )
      /\
      A. b e. ( Base ` S )
        E. c e. ( Base ` R )
          E. n e. NN0
            E. v e. ( Unit ` S )
              (
                (
                  (
                    n
                    ( .g ` ( mulGrp ` S ) )
                    ( H ` a )
                  )
                  ( .r ` S )
                  v
                )
                =
                ( 1r ` S )
                /\
                b = ( ( H ` c ) ( .r ` S ) v )
              )
      /\
      A. c e. ( Base ` R )
        (
          ( H ` c ) = ( 0g ` S )
          ->
          E. n e. NN0
            (
              (
                n
                ( .g ` ( mulGrp ` R ) )
                a
              )
              ( .r ` R )
              c
            )
            =
            ( 0g ` R )
        )
    )
  ) $.
$}

${
  $d D H J O P R U V X a x $.

  q8066795-affine-definition $a |- (
    Q8066795Affine X U
    <->
    E. J E. O E. R E. P E. D
      (
        J = ( X ` 1 )
        /\
        O = ( X ` 2 )
        /\
        R = ( X ` 3 )
        /\
        P = ( X ` 4 )
        /\
        D = ( X ` 5 )
        /\
        U e. J
        /\
        (
          x e. U |->
          ( P ` <. U , x >. )
        )
        :
        U -1-1-onto-> ( PrmIdeal ` ( O ` U ) )
        /\
        A. a e. ( Base ` ( O ` U ) )
          (
            ( D ` <. U , a >. )
            =
            {
              x e. U |
              -. a e. ( P ` <. U , x >. )
            }
            /\
            (
              Q8066795Localization
              ( O ` U )
              ( O ` ( D ` <. U , a >. ) )
              ( R ` <. U , ( D ` <. U , a >. ) >. )
              a
            )
          )
        /\
        A. V e. J
          (
            V C_ U
            ->
            A. x e. V
              E. a e. ( Base ` ( O ` U ) )
                (
                  x e. ( D ` <. U , a >. )
                  /\
                  ( D ` <. U , a >. ) C_ V
                )
          )
      )
  ) $.
$}

${
  $d A B D J O P R U V W X a b s $.

  q8066795-scheme-definition $a |- (
    Q8066795Scheme X
    <->
    E. B E. J E. O E. R E. P E. D
      (
        B = ( X ` 0 )
        /\
        J = ( X ` 1 )
        /\
        O = ( X ` 2 )
        /\
        R = ( X ` 3 )
        /\
        P = ( X ` 4 )
        /\
        D = ( X ` 5 )
        /\
        X Fn ( 0 ... 5 )
        /\
        J e. Top
        /\
        U. J = B
        /\
        O : J --> CRing
        /\
        R Fn
          U_ U e. J
            ( { U } X. { V e. J | V C_ U } )
        /\
        P Fn
          U_ U e. J
            ( { U } X. U )
        /\
        D Fn
          U_ U e. J
            (
              { U }
              X.
              ( Base ` ( O ` U ) )
            )
        /\
        A. U e. J
          A. V e. J
            (
              V C_ U
              ->
              ( R ` <. U , V >. )
              e.
              ( ( O ` U ) RingHom ( O ` V ) )
            )
        /\
        A. U e. J
          (
            R ` <. U , U >.
          )
          =
          ( _I |` ( Base ` ( O ` U ) ) )
        /\
        A. U e. J
          A. V e. J
            A. W e. J
              (
                (
                  W C_ V
                  /\
                  V C_ U
                )
                ->
                (
                  ( R ` <. V , W >. )
                  o.
                  ( R ` <. U , V >. )
                )
                =
                ( R ` <. U , W >. )
              )
        /\
        A. U e. J
          A. A
            A. s
              (
                (
                  A C_ { V e. J | V C_ U }
                  /\
                  U = U. A
                  /\
                  s Fn A
                  /\
                  A. V e. A
                    ( s ` V ) e. ( Base ` ( O ` V ) )
                  /\
                  A. V e. A
                    A. W e. A
                      (
                        (
                          R
                          `
                          <. V , ( V i^i W ) >.
                        )
                        `
                        ( s ` V )
                      )
                      =
                      (
                        (
                          R
                          `
                          <. W , ( V i^i W ) >.
                        )
                        `
                        ( s ` W )
                      )
                )
                ->
                E! a e. ( Base ` ( O ` U ) )
                  A. V e. A
                    (
                      (
                        R ` <. U , V >.
                      )
                      `
                      a
                    )
                    =
                    ( s ` V )
              )
        /\
        A. x e. B
          E. U e. J
            (
              x e. U
              /\
              Q8066795Affine X U
            )
      )
  ) $.
$}

${
  $d J O R U V X a b x $.

  q8066795-germ-unit-definition $a |- (
    Q8066795GermUnit X U x a
    <->
    E. J E. O E. R
      (
        J = ( X ` 1 )
        /\
        O = ( X ` 2 )
        /\
        R = ( X ` 3 )
        /\
        U e. J
        /\
        x e. U
        /\
        a e. ( Base ` ( O ` U ) )
        /\
        E. V e. J
          E. b e. ( Base ` ( O ` V ) )
            (
              V C_ U
              /\
              x e. V
              /\
              (
                (
                  ( R ` <. U , V >. )
                  `
                  a
                )
                ( .r ` ( O ` V ) )
                b
              )
              =
              ( 1r ` ( O ` V ) )
            )
      )
  ) $.
$}

${
  $d F H I J K O R U V X Y a f x $.

  q8066795-morphism-definition $a |- (
    Q8066795Morphism f
    <->
    E. X E. Y E. F E. I E. H
      E. J E. K E. O E. R
        (
          X = ( f ` 0 )
          /\
          Y = ( f ` 1 )
          /\
          F = ( f ` 2 )
          /\
          I = ( f ` 3 )
          /\
          H = ( f ` 4 )
          /\
          J = ( X ` 1 )
          /\
          K = ( Y ` 1 )
          /\
          O = ( X ` 2 )
          /\
          R = ( Y ` 2 )
          /\
          f Fn ( 0 ... 4 )
          /\
          Q8066795Scheme X
          /\
          Q8066795Scheme Y
          /\
          F : ( X ` 0 ) --> ( Y ` 0 )
          /\
          I : K --> J
          /\
          H Fn K
          /\
          A. U e. K
            (
              ( I ` U ) = ( `' F " U )
              /\
              ( H ` U )
              e.
              (
                ( R ` U )
                RingHom
                ( O ` ( I ` U ) )
              )
            )
          /\
          A. U e. K
            A. V e. K
              (
                V C_ U
                ->
                (
                  (
                    (
                      X ` 3
                    )
                    `
                    <. ( I ` U ) , ( I ` V ) >.
                  )
                  o.
                  ( H ` U )
                )
                =
                (
                  ( H ` V )
                  o.
                  (
                    (
                      Y ` 3
                    )
                    `
                    <. U , V >.
                  )
                )
              )
          /\
          A. x e. ( X ` 0 )
            A. U e. K
              A. a e. ( Base ` ( R ` U ) )
                (
                  ( F ` x ) e. U
                  /\
                  (
                    Q8066795GermUnit
                    X
                    ( I ` U )
                    x
                    ( ( H ` U ) ` a )
                  )
                  ->
                  Q8066795GermUnit
                  Y
                  U
                  ( F ` x )
                  a
                )
        )
  ) $.
$}

${
  $d G H N R S a b c $.

  q8066795-finite-module-definition $a |- (
    Q8066795FiniteModule R S H
    <->
    (
      H e. ( R RingHom S )
      /\
      E. G e. Fin
        (
          G C_ ( Base ` S )
          /\
          A. N
            (
              (
                N C_ ( Base ` S )
                /\
                ( 0g ` S ) e. N
                /\
                A. b e. N
                  ( ( -g ` S ) ` b ) e. N
                /\
                A. b e. N
                  A. c e. N
                    ( b ( +g ` S ) c ) e. N
                /\
                A. a e. ( Base ` R )
                  A. b e. N
                    ( ( H ` a ) ( .r ` S ) b ) e. N
                /\
                G C_ N
              )
              ->
              N = ( Base ` S )
            )
        )
    )
  ) $.
$}

${
  $d A G H R S a b c $.

  q8066795-finite-type-definition $a |- (
    Q8066795FiniteType R S H
    <->
    (
      H e. ( R RingHom S )
      /\
      E. G e. Fin
        (
          G C_ ( Base ` S )
          /\
          A. A
            (
              (
                A C_ ( Base ` S )
                /\
                A. a e. ( Base ` R )
                  ( H ` a ) e. A
                /\
                ( 0g ` S ) e. A
                /\
                ( 1r ` S ) e. A
                /\
                A. b e. A
                  ( ( -g ` S ) ` b ) e. A
                /\
                A. b e. A
                  A. c e. A
                    (
                      ( b ( +g ` S ) c ) e. A
                      /\
                      ( b ( .r ` S ) c ) e. A
                    )
                /\
                G C_ A
              )
              ->
              A = ( Base ` S )
            )
        )
    )
  ) $.
$}

${
  $d F H I X f $.

  q8066795-identity-definition $a |- (
    Q8066795Identity f X
    <->
    E. F E. I E. H
      (
        Q8066795Morphism f
        /\
        ( f ` 0 ) = X
        /\
        ( f ` 1 ) = X
        /\
        F = ( f ` 2 )
        /\
        I = ( f ` 3 )
        /\
        H = ( f ` 4 )
        /\
        F = ( _I |` ( X ` 0 ) )
        /\
        I = ( _I |` ( X ` 1 ) )
        /\
        A. U e. ( X ` 1 )
          ( H ` U )
          =
          ( _I |` ( Base ` ( ( X ` 2 ) ` U ) ) )
      )
  ) $.
$}

${
  $d F G H I J K U f g h $.

  q8066795-compose-definition $a |- (
    Q8066795Compose f g h
    <->
    E. F E. G E. H E. I E. J E. K
      (
        Q8066795Morphism f
        /\
        Q8066795Morphism g
        /\
        Q8066795Morphism h
        /\
        ( f ` 1 ) = ( g ` 0 )
        /\
        ( h ` 0 ) = ( f ` 0 )
        /\
        ( h ` 1 ) = ( g ` 1 )
        /\
        F = ( f ` 2 )
        /\
        G = ( g ` 2 )
        /\
        H = ( h ` 2 )
        /\
        I = ( f ` 3 )
        /\
        J = ( g ` 3 )
        /\
        K = ( h ` 3 )
        /\
        H = ( G o. F )
        /\
        K = ( I o. J )
        /\
        A. U e. ( ( g ` 1 ) ` 1 )
          (
            ( h ` 4 ) ` U
          )
          =
          (
            (
              ( f ` 4 ) ` ( J ` U )
            )
            o.
            ( ( g ` 4 ) ` U )
          )
      )
  ) $.
$}

${
  $d C F J X Y f $.

  q8066795-closed-map-definition $a |- (
    Q8066795ClosedMap f
    <->
    E. X E. Y E. F E. J
      (
        Q8066795Morphism f
        /\
        X = ( f ` 0 )
        /\
        Y = ( f ` 1 )
        /\
        F = ( f ` 2 )
        /\
        J = ( Y ` 1 )
        /\
        A. C
          (
            (
              C C_ ( X ` 0 )
              /\
              ( ( X ` 0 ) \ C ) e. ( X ` 1 )
            )
            ->
            (
              ( Y ` 0 )
              \
              ( F " C )
            )
            e.
            J
          )
      )
  ) $.
$}

${
  $d F H I U X Y f $.

  q8066795-closed-immersion-definition $a |- (
    Q8066795ClosedImmersion f
    <->
    E. X E. Y E. F E. I E. H
      (
        Q8066795Morphism f
        /\
        X = ( f ` 0 )
        /\
        Y = ( f ` 1 )
        /\
        F = ( f ` 2 )
        /\
        I = ( f ` 3 )
        /\
        H = ( f ` 4 )
        /\
        F : ( X ` 0 ) -1-1-> ( Y ` 0 )
        /\
        (
          ( Y ` 0 )
          \
          ran F
        )
        e.
        ( Y ` 1 )
        /\
        A. U e. ( Y ` 1 )
          (
            Q8066795Affine Y U
            ->
            (
              Q8066795Affine X ( I ` U )
              /\
              ( H ` U )
              :
              ( Base ` ( ( Y ` 2 ) ` U ) )
              -onto->
              ( Base ` ( ( X ` 2 ) ` ( I ` U ) ) )
            )
          )
      )
  ) $.
$}

${
  $d T W a b c d f g k p q u v $.

  q8066795-pullback-definition $a |- (
    Q8066795Pullback f g W p q
    <->
    (
      Q8066795Morphism f
      /\
      Q8066795Morphism g
      /\
      ( f ` 1 ) = ( g ` 1 )
      /\
      Q8066795Scheme W
      /\
      Q8066795Morphism p
      /\
      Q8066795Morphism q
      /\
      ( p ` 0 ) = W
      /\
      ( p ` 1 ) = ( f ` 0 )
      /\
      ( q ` 0 ) = W
      /\
      ( q ` 1 ) = ( g ` 0 )
      /\
      E. a E. b
        (
          Q8066795Compose p f a
          /\
          Q8066795Compose q g b
          /\
          a = b
        )
      /\
      A. T
        A. u
          A. v
            (
              (
                Q8066795Morphism u
                /\
                Q8066795Morphism v
                /\
                ( u ` 0 ) = T
                /\
                ( v ` 0 ) = T
                /\
                ( u ` 1 ) = ( f ` 0 )
                /\
                ( v ` 1 ) = ( g ` 0 )
                /\
                E. a E. b
                  (
                    Q8066795Compose u f a
                    /\
                    Q8066795Compose v g b
                    /\
                    a = b
                  )
              )
              ->
              E. k
                (
                  Q8066795Morphism k
                  /\
                  ( k ` 0 ) = T
                  /\
                  ( k ` 1 ) = W
                  /\
                  E. a E. b
                    (
                      Q8066795Compose k p a
                      /\
                      Q8066795Compose k q b
                      /\
                      a = u
                      /\
                      b = v
                    )
                  /\
                  A. d
                    (
                      (
                        Q8066795Morphism d
                        /\
                        ( d ` 0 ) = T
                        /\
                        ( d ` 1 ) = W
                        /\
                        E. a E. b
                          (
                            Q8066795Compose d p a
                            /\
                            Q8066795Compose d q b
                            /\
                            a = u
                            /\
                            b = v
                          )
                      )
                      ->
                      d = k
                    )
                )
            )
    )
  ) $.
$}

${
  $d W a b d f i p q $.

  q8066795-separated-definition $a |- (
    Q8066795Separated f
    <->
    (
      Q8066795Morphism f
      /\
      E. W E. p E. q
        (
          Q8066795Pullback f f W p q
          /\
          E. d E. i
            (
              Q8066795Identity i ( f ` 0 )
              /\
              Q8066795Morphism d
              /\
              ( d ` 0 ) = ( f ` 0 )
              /\
              ( d ` 1 ) = W
              /\
              E. a E. b
                (
                  Q8066795Compose d p a
                  /\
                  Q8066795Compose d q b
                  /\
                  a = i
                  /\
                  b = i
                )
              /\
              Q8066795ClosedImmersion d
            )
        )
    )
  ) $.
$}

${
  $d W f g p q $.

  q8066795-universally-closed-definition $a |- (
    Q8066795UniversallyClosed f
    <->
    (
      Q8066795Morphism f
      /\
      A. g
        (
          (
            Q8066795Morphism g
            /\
            ( g ` 1 ) = ( f ` 1 )
          )
          ->
          E. W E. p E. q
            (
              Q8066795Pullback f g W p q
              /\
              Q8066795ClosedMap q
            )
        )
    )
  ) $.
$}

${
  $d F H I K R U V X Y f $.

  q8066795-locally-finite-type-definition $a |- (
    Q8066795LocallyFiniteType f
    <->
    E. X E. Y E. F E. I E. H
      (
        Q8066795Morphism f
        /\
        X = ( f ` 0 )
        /\
        Y = ( f ` 1 )
        /\
        F = ( f ` 2 )
        /\
        I = ( f ` 3 )
        /\
        H = ( f ` 4 )
        /\
        A. U e. ( Y ` 1 )
          A. V e. ( X ` 1 )
            (
              (
                Q8066795Affine Y U
                /\
                Q8066795Affine X V
                /\
                V C_ ( I ` U )
              )
              ->
              E. K
                (
                  K
                  =
                  (
                    (
                      ( X ` 3 )
                      `
                      <. ( I ` U ) , V >.
                    )
                    o.
                    ( H ` U )
                  )
                  /\
                  Q8066795FiniteType
                  ( ( Y ` 2 ) ` U )
                  ( ( X ` 2 ) ` V )
                  K
                )
            )
      )
  ) $.
$}

${
  q8066795-proper-definition $a |- (
    Q8066795Proper f
    <->
    (
      Q8066795Separated f
      /\
      Q8066795UniversallyClosed f
      /\
      Q8066795LocallyFiniteType f
    )
  ) $.
$}

${
  $d H I U V X Y f $.

  q8066795-finite-on-open-definition $a |- (
    Q8066795FiniteOnOpen f V
    <->
    E. X E. Y E. I E. H
      (
        Q8066795Morphism f
        /\
        X = ( f ` 0 )
        /\
        Y = ( f ` 1 )
        /\
        I = ( f ` 3 )
        /\
        H = ( f ` 4 )
        /\
        V e. ( Y ` 1 )
        /\
        A. U e. ( Y ` 1 )
          (
            (
              U C_ V
              /\
              Q8066795Affine Y U
            )
            ->
            (
              Q8066795Affine X ( I ` U )
              /\
              Q8066795FiniteModule
              ( ( Y ` 2 ) ` U )
              ( ( X ` 2 ) ` ( I ` U ) )
              ( H ` U )
            )
          )
      )
  ) $.
$}

${
  $d F V X Y f x y $.

  thousand-theorems-q8066795-zariski-s-main-theorem $a |-
    A. f
      (
        Q8066795Morphism f
        ->
        E. X E. Y E. F
          (
            X = ( f ` 0 )
            /\
            Y = ( f ` 1 )
            /\
            F = ( f ` 2 )
            /\
            A. y e. ( Y ` 0 )
              (
                (
                  Q8066795Proper f
                  /\
                  { x e. ( X ` 0 ) | ( F ` x ) = y } e. Fin
                )
                ->
                E. V e. ( Y ` 1 )
                  (
                    y e. V
                    /\
                    Q8066795FiniteOnOpen f V
                  )
              )
          )
      )
  $.
$}
