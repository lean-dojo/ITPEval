$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1008566
  (thousand-theorems__metamath__Q1008566), "Gauss-Lucas theorem": every
  critical point of a nonconstant complex polynomial lies in the real convex
  hull of its complex roots, with the corresponding root-weighted
  center-of-mass identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  QGLRoots is the set of complex roots of a SetMM complex polynomial
  function. QGLConvex expresses convexity over the real scalars on the complex
  plane, and QGLHull is the intersection of all such convex supersets.

  QGLCompleteRoots(P,r) says that r lists all roots of P with multiplicity:
  P is a nonzero leading constant times the product of the linear factors
  indexed from 1 through deg(P). QGLMultiplicity counts occurrences of a
  given root in that list. QGLWeight is exactly the source weight: a delta
  weight when the critical point is a root, and otherwise root multiplicity
  divided by squared distance. QGLCenter sums these weights once over each
  distinct root, matching roots.toFinset.centerMass.

  The two final unproved $a assertions render the two Lean declarations. The
  complete-root enumeration and leading coefficient remain internally
  quantified. SetMM's first complex derivative of a polynomial function is
  its formal polynomial derivative, and no finiteness restriction is placed
  on the ambient complex domain.
$)

$c QGLRoots QGLConvex QGLHull QGLCompleteRoots QGLMultiplicity
   QGLWeight QGLCenter $.

qgl-roots-syntax $a class ( QGLRoots A ) $.
qgl-convex-syntax $a wff ( QGLConvex A ) $.
qgl-hull-syntax $a class ( QGLHull A ) $.
qgl-complete-roots-syntax $a wff ( QGLCompleteRoots A B ) $.
qgl-multiplicity-syntax $a class ( QGLMultiplicity A B C ) $.
qgl-weight-syntax $a class ( QGLWeight A B C D ) $.
qgl-center-syntax $a wff ( QGLCenter A B C ) $.

${
  $d A x $.

  qgl-roots-definition $a |- ( QGLRoots A ) =
    { x e. CC | ( A ` x ) = 0 }
  $.
$}

${
  $d A t x y $.

  qgl-convex-definition $a |- (
    ( QGLConvex A )
    <->
    (
      A C_ CC
      /\
      A. x e. A
        A. y e. A
          A. t e. RR
            (
              (
                0 <_ t
                /\
                t <_ 1
              )
              ->
              (
                (
                  ( ( 1 - t ) x. x )
                  +
                  ( t x. y )
                )
                e. A
              )
            )
    )
  ) $.
$}

${
  $d A s $.

  qgl-hull-definition $a |- ( QGLHull A ) =
    |^| { s e. ~P CC | ( A C_ s /\ ( QGLConvex s ) ) }
  $.
$}

${
  $d A B a i x $.

  qgl-complete-roots-definition $a |- (
    ( QGLCompleteRoots A B )
    <->
    E. a e. ( CC \ { 0 } )
      A. x e. CC
        ( A ` x )
        =
        (
          a
          x.
          prod_ i e. ( 1 ... ( deg ` A ) )
            ( x - ( B ` i ) )
        )
  ) $.
$}

${
  $d A C D i $.

  qgl-multiplicity-definition $a |- ( QGLMultiplicity A C D ) =
    ( # ` { i e. ( 1 ... ( deg ` A ) ) | ( C ` i ) = D } )
  $.
$}

${
  $d A B C D $.

  qgl-weight-definition $a |- ( QGLWeight A B C D ) =
    if (
      ( A ` B ) = 0
      ,
      if ( D = B , 1 , 0 )
      ,
      (
        ( QGLMultiplicity A C D )
        /
        ( ( abs ` ( B - D ) ) ^ 2 )
      )
    )
  $.
$}

${
  $d A B C w $.

  qgl-center-definition $a |- (
    ( QGLCenter A B C )
    <->
    B
    =
    (
      (
        1
        /
        sum_ w e. ( QGLRoots A )
          ( QGLWeight A B C w )
      )
      x.
      (
        sum_ w e. ( QGLRoots A )
          (
            ( QGLWeight A B C w )
            x.
            w
          )
      )
    )
  ) $.
$}

${
  $d P r z $.

  thousand-theorems-q1008566-center-mass $a |-
    A. P e. ( Poly ` CC )
      A. z e. CC
        (
          (
            0 < ( deg ` P )
            /\
            ( ( ( CC Dn P ) ` 1 ) ` z ) = 0
          )
          ->
          E. r e. ( CC ^m ( 1 ... ( deg ` P ) ) )
            (
              ( QGLCompleteRoots P r )
              /\
              ( QGLCenter P z r )
            )
        )
  $.
$}

${
  $d P z $.

  thousand-theorems-q1008566-gauss-lucas $a |-
    A. P e. ( Poly ` CC )
      (
        0 < ( deg ` P )
        ->
        A. z e. CC
          (
            ( ( ( CC Dn P ) ` 1 ) ` z ) = 0
            ->
            z e. ( QGLHull ( QGLRoots P ) )
          )
      )
  $.
$}
