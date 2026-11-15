$(
  Statement-only formalization of "Pick's Theorem" from the Hundred
  Theorems corpus artifact 092 (hundred-theorems__metamath__092): the area
  enclosed by a simple closed lattice polygon equals its number of interior
  lattice points plus half its number of boundary lattice points minus one.
  This file contains no proof.
$)

$[ library/set.mm $]

$(
  The Euclidean plane is identified isometrically with CC. A polygon is
  represented by a vertex function V on 0 ... N, with V(0) = V(N). Its
  boundary is the union of the closed segments between successive vertices.

  HT092Simple requires at least three edges, distinct non-closing vertices,
  and exactly the intersections permitted between equal or adjacent edges.
  This is equivalent to the simple closed polygonal-path hypotheses in the
  HOL Light and Isabelle sources. HT092Inside is the bounded connected
  component of the boundary complement. HT092Area is planar Lebesgue area,
  expressed as an iterated integral of an indicator. HT092Integral says that
  both coordinates are integers.

  The final declaration is the unproved statement itself.
$)

$c HT092Segment HT092Image HT092Simple HT092Inside $.
$c HT092Integral HT092InteriorLattice HT092BoundaryLattice $.
$c HT092Indicator HT092Row HT092Area $.

ht092-segment-syntax $a class ( HT092Segment A B ) $.
ht092-image-syntax $a class ( HT092Image V N ) $.
ht092-simple-syntax $a wff ( HT092Simple V N ) $.
ht092-inside-syntax $a class ( HT092Inside V N ) $.
ht092-integral-syntax $a wff ( HT092Integral Z ) $.
ht092-interior-lattice-syntax $a class ( HT092InteriorLattice V N ) $.
ht092-boundary-lattice-syntax $a class ( HT092BoundaryLattice V N ) $.
ht092-indicator-syntax $a class ( HT092Indicator S X Y ) $.
ht092-row-syntax $a class ( HT092Row S X ) $.
ht092-area-syntax $a class ( HT092Area S ) $.

${
  $d t z A B $.

  ht092-segment-definition $a |- (
    ( HT092Segment A B )
    =
    { z e. CC |
      E. t e. ( 0 [,] 1 )
        z = ( ( ( 1 - t ) x. A ) + ( t x. B ) )
    }
  ) $.
$}

${
  $d k n v $.

  ht092-image-definition $a |- (
    ( HT092Image V N )
    =
    U_ k e. ( 0 ..^ N )
      ( HT092Segment ( V ` k ) ( V ` ( k + 1 ) ) )
  ) $.
$}

${
  $d i j z V N $.

  ht092-simple-definition $a |- (
    ( HT092Simple V N )
    <->
    (
      (
        3 <_ N
        /\
        V : ( 0 ... N ) --> CC
      )
      /\
      (
        ( V ` 0 ) = ( V ` N )
        /\
        (
          A. i e. ( 0 ..^ N ) A. j e. ( 0 ..^ N )
            ( ( V ` i ) = ( V ` j ) -> i = j )
          /\
          A. i e. ( 0 ..^ N ) A. j e. ( 0 ..^ N ) A. z e. CC
            (
              (
                z e. ( HT092Segment ( V ` i ) ( V ` ( i + 1 ) ) )
                /\
                z e. ( HT092Segment ( V ` j ) ( V ` ( j + 1 ) ) )
              )
              <->
              (
                (
                  i = j
                  /\
                  z e. ( HT092Segment ( V ` i ) ( V ` ( i + 1 ) ) )
                )
                \/
                (
                  (
                    j = ( i + 1 )
                    /\
                    z = ( V ` j )
                  )
                  \/
                  (
                    (
                      i = ( j + 1 )
                      /\
                      z = ( V ` i )
                    )
                    \/
                    (
                      (
                        ( i = 0 /\ j = ( N - 1 ) )
                        /\
                        z = ( V ` 0 )
                      )
                      \/
                      (
                        ( j = 0 /\ i = ( N - 1 ) )
                        /\
                        z = ( V ` 0 )
                      )
                    )
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
  $d c r w z V N $.

  ht092-inside-definition $a |- (
    ( HT092Inside V N )
    =
    { z e. ( CC \ ( HT092Image V N ) ) |
      E. r e. RR+
        A. w e.
          U. { c e. ~P ( CC \ ( HT092Image V N ) ) |
            (
              z e. c
              /\
              (
                (
                  (
                    ( TopOpen ` CCfld )
                    |`t ( CC \ ( HT092Image V N ) )
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
  ht092-integral-definition $a |- (
    ( HT092Integral Z )
    <->
    (
      ( Re ` Z ) e. ZZ
      /\
      ( Im ` Z ) e. ZZ
    )
  ) $.
$}

${
  $d z V N $.

  ht092-interior-lattice-definition $a |- (
    ( HT092InteriorLattice V N )
    =
    { z e. ( HT092Inside V N ) | ( HT092Integral z ) }
  ) $.

  ht092-boundary-lattice-definition $a |- (
    ( HT092BoundaryLattice V N )
    =
    { z e. ( HT092Image V N ) | ( HT092Integral z ) }
  ) $.
$}

${
  $d S X Y $.

  ht092-indicator-definition $a |- (
    ( HT092Indicator S X Y )
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

  ht092-row-definition $a |- (
    ( HT092Row S X )
    =
    S. RR ( HT092Indicator S X y ) _d y
  ) $.
$}

${
  $d x S $.

  ht092-area-definition $a |- (
    ( HT092Area S )
    =
    S. RR ( HT092Row S x ) _d x
  ) $.
$}

${
  $d k V N $.

  hundred-theorems-092-pick $a |- (
    A. n e. NN A. v
      (
        (
          ( HT092Simple v n )
          /\
          A. k e. ( 0 ... n )
            ( HT092Integral ( v ` k ) )
        )
        ->
        (
          ( HT092Area ( HT092Inside v n ) )
          =
          (
            ( # ` ( HT092InteriorLattice v n ) )
            +
            (
              ( # ` ( HT092BoundaryLattice v n ) )
              /
              2
            )
          )
          -
          1
        )
      )
  ) $.
$}
