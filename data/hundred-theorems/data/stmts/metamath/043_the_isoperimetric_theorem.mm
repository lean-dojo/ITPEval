$(
  Statement-only formalization of "The Isoperimetric Theorem" from Hundred
  Theorems item 043. It states the sharp area bound for a rectifiable simple
  closed plane curve of prescribed length, together with the equality
  characterization by a Euclidean circle. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The source spaces real^1 and real^2 are identified isometrically with RR and
  CC. A source curve g : real^1 -> real^2 is therefore represented by a total
  function G : RR --> CC, while its path image is the image of 0 [,] 1.

  The definitions below are set-theoretic abbreviations over set.mm:

  * HT043Path requires continuity on the closed unit interval in the standard
    real and complex topologies.
  * HT043Simple is injectivity on that interval apart from the two endpoints,
    exactly the simple_path convention for a closed path.
  * HT043Length is the supremum of all polygonal partition sums. Thus
    HT043Rectifiable says that this variation is a real number.
  * HT043Inside is the union of the bounded connected components of the
    complement of the path image in the standard complex topology.
  * HT043Area is the iterated Lebesgue integral of the indicator after the
    identification (x,y) |-> x + i y. For the inside of a rectifiable Jordan
    curve this equals planar Lebesgue measure.
  * HT043Sphere is the Euclidean sphere {z : abs(z-a) = r} in the plane.

  The final $a assertion is the statement itself and is intentionally
  unproved.
$)

$c HT043Image HT043Path HT043Simple HT043Length HT043Rectifiable $.
$c HT043Inside HT043Indicator HT043Row HT043Area HT043Sphere $.

ht043-image-syntax $a class ( HT043Image G ) $.
ht043-path-syntax $a wff ( HT043Path G ) $.
ht043-simple-syntax $a wff ( HT043Simple G ) $.
ht043-length-syntax $a class ( HT043Length G ) $.
ht043-rectifiable-syntax $a wff ( HT043Rectifiable G ) $.
ht043-inside-syntax $a class ( HT043Inside G ) $.
ht043-indicator-syntax $a class ( HT043Indicator S X Y ) $.
ht043-row-syntax $a class ( HT043Row S X ) $.
ht043-area-syntax $a class ( HT043Area S ) $.
ht043-sphere-syntax $a class ( HT043Sphere A R ) $.

${
  ht043-image-definition $a |- (
    ( HT043Image G ) = ( G " ( 0 [,] 1 ) )
  ) $.
$}

${
  ht043-path-definition $a |- (
    ( HT043Path G )
    <->
    (
      G : RR --> CC
      /\
      ( G |` ( 0 [,] 1 ) ) e.
        (
          ( ( TopOpen ` RRfld ) |`t ( 0 [,] 1 ) )
          Cn
          ( TopOpen ` CCfld )
        )
    )
  ) $.
$}

${
  $d x y G $.

  ht043-simple-definition $a |- (
    ( HT043Simple G )
    <->
    (
      ( HT043Path G )
      /\
      A. x e. ( 0 [,] 1 ) A. y e. ( 0 [,] 1 )
        (
          ( G ` x ) = ( G ` y )
          ->
          (
            x = y
            \/
            (
              ( x = 0 /\ y = 1 )
              \/
              ( x = 1 /\ y = 0 )
            )
          )
        )
    )
  ) $.
$}

${
  $d j k n p s G $.

  ht043-length-definition $a |- (
    ( HT043Length G )
    =
    sup
      (
        { s e. RR |
          E. n e. NN E. p
            (
              (
                p : ( 0 ... n ) --> RR
                /\
                ( ( p ` 0 ) = 0 /\ ( p ` n ) = 1 )
              )
              /\
              (
                A. j e. ( 0 ..^ n )
                  ( p ` j ) < ( p ` ( j + 1 ) )
                /\
                s =
                  sum_ k e. ( 0 ..^ n )
                    (
                      abs `
                        (
                          ( G ` ( p ` ( k + 1 ) ) )
                          -
                          ( G ` ( p ` k ) )
                        )
                    )
              )
            )
        } ,
        RR ,
        <
      )
  ) $.
$}

${
  ht043-rectifiable-definition $a |- (
    ( HT043Rectifiable G )
    <->
    ( ( HT043Path G ) /\ ( HT043Length G ) e. RR )
  ) $.
$}

${
  $d c r w z G $.

  ht043-inside-definition $a |- (
    ( HT043Inside G )
    =
    { z e. ( CC \ ( HT043Image G ) ) |
      E. r e. RR+
        A. w e.
          U. { c e. ~P ( CC \ ( HT043Image G ) ) |
            (
              z e. c
              /\
              (
                (
                  (
                    ( TopOpen ` CCfld )
                    |`t ( CC \ ( HT043Image G ) )
                  )
                  |`t c
                )
                e. Conn
              )
            )
          }
          ( ( abs ` w ) < r )
    }
  ) $.
$}

${
  $d S X Y $.

  ht043-indicator-definition $a |- (
    ( HT043Indicator S X Y )
    =
    if
      (
        ( X + ( _i x. Y ) ) e. S ,
        1 ,
        0
      )
  ) $.
$}

${
  $d y S X $.

  ht043-row-definition $a |- (
    ( HT043Row S X )
    =
    S. RR ( HT043Indicator S X y ) _d y
  ) $.
$}

${
  $d x S $.

  ht043-area-definition $a |- (
    ( HT043Area S )
    =
    S. RR ( HT043Row S x ) _d x
  ) $.
$}

${
  $d z A R $.

  ht043-sphere-definition $a |- (
    ( HT043Sphere A R )
    =
    { z e. CC | ( abs ` ( z - A ) ) = R }
  ) $.
$}

${
  $d a G L r $.

  hundred-theorems-043-isoperimetric-theorem $a |- (
    (
        (
          (
            ( HT043Rectifiable G )
            /\
            ( HT043Simple G )
          )
          /\
          (
            ( G ` 1 ) = ( G ` 0 )
            /\
            ( HT043Length G ) = L
          )
        )
        ->
        (
          ( HT043Area ( HT043Inside G ) )
            <_ ( ( L ^ 2 ) / ( 4 x. _pi ) )
          /\
          (
            ( HT043Area ( HT043Inside G ) )
              = ( ( L ^ 2 ) / ( 4 x. _pi ) )
            ->
            E. a e. CC E. r e. RR
              ( HT043Image G ) = ( HT043Sphere a r )
          )
        )
    )
  ) $.
$}
