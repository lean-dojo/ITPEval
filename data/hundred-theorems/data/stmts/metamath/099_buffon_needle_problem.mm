$(
  Statement-only formalization of Hundred Theorems corpus artifact 099,
  "Buffon Needle Problem". It states Buffon's needle crossing probability for
  positive needle length and line spacing, using independent uniform real
  random variables for the distance from the needle center to the nearest
  line and for its angle. The general integral identity and the short- and
  long-needle closed forms are included. This file contains no proof.
$)

$[ library/set.mm $]

$(
  HT099Uniform gives the exact cumulative-distribution characterization of a
  uniform real random variable on [ A , B ]. HT099Independent expands
  independence as the product identity for every pair of Borel preimages.
  HT099Crossing is the event

    X <= ( L / 2 ) sin T.

  Thus X is uniform on [ 0 , D / 2 ] and T is uniform on [ 0 , pi ], exactly
  the distance-and-angle model used by the HOL Light source and equivalent to
  the signed-center product-space models in the Isabelle and Lean sources.
  The integral below uses ( 0 , pi ); this equals the sources' integral over
  [ 0 , pi ] because the two endpoints have Lebesgue measure zero.

  Every declaration is an unproved $a statement. There is no $p proof
  statement in this file.
$)

$c HT099Uniform HT099Independent HT099Crossing $.

ht099-uniform-syntax $a wff ( HT099Uniform P X A B ) $.
ht099-independent-syntax $a wff ( HT099Independent P X T ) $.
ht099-crossing-syntax $a class ( HT099Crossing P X T L ) $.

${
  $d A B P X t x $.

  ht099-uniform-definition $a |- (
    ( HT099Uniform P X A B )
    <->
    (
      P e. Prob
      /\
      (
        X e. ( dom P MblFnM BrSiga )
        /\
        (
          A e. RR
          /\
          (
            B e. RR
            /\
            (
              A < B
              /\
              A. t e. RR
                (
                  P `
                  { x e. U. dom P | ( X ` x ) <_ t }
                )
                =
                if (
                  t < A ,
                  0 ,
                  if (
                    B < t ,
                    1 ,
                    ( t - A ) / ( B - A )
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
  $d P T X a b $.

  ht099-independent-definition $a |- (
    ( HT099Independent P X T )
    <->
    A. a e. BrSiga A. b e. BrSiga
      (
        P ` (
          ( `' X " a )
          i^i
          ( `' T " b )
        )
      )
      =
      (
        ( P ` ( `' X " a ) )
        *e
        ( P ` ( `' T " b ) )
      )
  ) $.
$}

${
  $d L P T X x $.

  ht099-crossing-definition $a |- (
    HT099Crossing P X T L
    =
    { x e. U. dom P |
      ( X ` x )
      <_
      (
        ( L / 2 )
        x.
        ( sin ` ( T ` x ) )
      )
    }
  ) $.
$}

${
  $d D L P T X t $.

  ht099-buffon-needle $a |- (
    (
      0 < L
      /\
      (
        0 < D
        /\
        (
          ( HT099Uniform P X 0 ( D / 2 ) )
          /\
          (
            ( HT099Uniform P T 0 _pi )
            /\
            ( HT099Independent P X T )
          )
        )
      )
    )
    ->
    (
      (
        P ` ( HT099Crossing P X T L )
      )
      =
      (
        ( 2 / ( _pi x. D ) )
        x.
        S. ( 0 (,) _pi )
          if (
            ( D / 2 )
            <_
            (
              ( L / 2 )
              x.
              ( sin ` t )
            )
            ,
            ( D / 2 )
            ,
            (
              ( L / 2 )
              x.
              ( sin ` t )
            )
          )
          _d t
      )
      /\
      (
        (
          L <_ D
          ->
          (
            P ` ( HT099Crossing P X T L )
          )
          =
          (
            ( 2 x. L )
            /
            ( _pi x. D )
          )
        )
        /\
        (
          D <_ L
          ->
          (
            P ` ( HT099Crossing P X T L )
          )
          =
          (
            ( 2 / ( _pi x. D ) )
            x.
            (
              (
                L
                -
                (
                  sqrt
                  `
                  (
                    ( L ^ 2 )
                    -
                    ( D ^ 2 )
                  )
                )
              )
              +
              (
                D
                x.
                (
                  arccos
                  `
                  ( D / L )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}
