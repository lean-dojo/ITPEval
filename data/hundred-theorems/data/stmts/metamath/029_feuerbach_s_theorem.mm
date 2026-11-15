$(
  Statement-only formalization of Hundred Theorems item 029, "Feuerbach's
  Theorem". This file contains no proof.
$)

$[ library/set.mm $]

$(
  The Euclidean plane is the actual set RR X. RR. Coordinates, squared
  distance, distance, midpoint, collinearity, perpendicularity, circle
  membership, and circle tangency are all conservative definitions over
  set.mm's real arithmetic.

  The final assertion follows the Lean and HOL Light statement. For a
  noncollinear triangle, one circle passes through the three side midpoints.
  A second circle has three radius feet on the side lines, with each radius
  perpendicular to its side. The circles are equal or have exactly one common
  point. The auxiliary circle criterion used in the HOL Light proof is not an
  axiom here.
$)

$c HT029Plane HT029X HT029Y HT029DistanceSq HT029Distance $.
$c HT029Midpoint HT029Collinear HT029Perpendicular $.
$c HT029OnCircle HT029CirclesTangent $.

ht029-plane-syntax $a class HT029Plane $.
ht029-x-syntax $a class ( HT029X A ) $.
ht029-y-syntax $a class ( HT029Y A ) $.
ht029-distance-sq-syntax $a class ( HT029DistanceSq A B ) $.
ht029-distance-syntax $a class ( HT029Distance A B ) $.
ht029-midpoint-syntax $a wff ( HT029Midpoint A B C ) $.
ht029-collinear-syntax $a wff ( HT029Collinear A B C ) $.
ht029-perpendicular-syntax $a wff ( HT029Perpendicular A B C D ) $.
ht029-on-circle-syntax $a wff ( HT029OnCircle A R B ) $.
ht029-circles-tangent-syntax $a wff ( HT029CirclesTangent A R B S ) $.

ht029-plane-definition $a |- HT029Plane = ( RR X. RR ) $.

ht029-x-definition $a |- (
  HT029X A
  =
  ( 1st ` A )
) $.

ht029-y-definition $a |- (
  HT029Y A
  =
  ( 2nd ` A )
) $.

ht029-distance-sq-definition $a |- (
  HT029DistanceSq A B
  =
  (
    ( ( ( HT029X B ) - ( HT029X A ) ) ^ 2 )
    +
    ( ( ( HT029Y B ) - ( HT029Y A ) ) ^ 2 )
  )
) $.

ht029-distance-definition $a |- (
  HT029Distance A B
  =
  ( sqrt ` ( HT029DistanceSq A B ) )
) $.

ht029-midpoint-definition $a |- (
  ( HT029Midpoint A B C )
  <->
  (
    (
      ( A e. HT029Plane /\ B e. HT029Plane )
      /\
      C e. HT029Plane
    )
    /\
    (
      ( 2 x. ( HT029X C ) )
      =
      ( ( HT029X A ) + ( HT029X B ) )
      /\
      ( 2 x. ( HT029Y C ) )
      =
      ( ( HT029Y A ) + ( HT029Y B ) )
    )
  )
) $.

ht029-collinear-definition $a |- (
  ( HT029Collinear A B C )
  <->
  (
    (
      ( A e. HT029Plane /\ B e. HT029Plane )
      /\
      C e. HT029Plane
    )
    /\
    (
      (
        ( ( HT029X A ) - ( HT029X B ) )
        x.
        ( ( HT029Y C ) - ( HT029Y B ) )
      )
      =
      (
        ( ( HT029Y A ) - ( HT029Y B ) )
        x.
        ( ( HT029X C ) - ( HT029X B ) )
      )
    )
  )
) $.

ht029-perpendicular-definition $a |- (
  ( HT029Perpendicular A B C D )
  <->
  (
    (
      (
        ( A e. HT029Plane /\ B e. HT029Plane )
        /\
        C e. HT029Plane
      )
      /\
      D e. HT029Plane
    )
    /\
    (
      (
        (
          ( ( HT029X A ) - ( HT029X B ) )
          x.
          ( ( HT029X C ) - ( HT029X D ) )
        )
        +
        (
          ( ( HT029Y A ) - ( HT029Y B ) )
          x.
          ( ( HT029Y C ) - ( HT029Y D ) )
        )
      )
      =
      0
    )
  )
) $.

ht029-on-circle-definition $a |- (
  ( HT029OnCircle A R B )
  <->
  (
    (
      ( A e. HT029Plane /\ B e. HT029Plane )
      /\
      R e. RR
    )
    /\
    (
      0 <_ R
      /\
      ( HT029Distance A B ) = R
    )
  )
) $.

${
  $d A B R S x $.

  ht029-circles-tangent-definition $a |- (
    ( HT029CirclesTangent A R B S )
    <->
    (
      (
        (
          ( A e. HT029Plane /\ B e. HT029Plane )
          /\
          ( R e. RR /\ S e. RR )
        )
        /\
        ( 0 <_ R /\ 0 <_ S )
      )
      /\
      (
        ( A = B /\ R = S )
        \/
        E! x e. HT029Plane
          (
            ( HT029OnCircle A R x )
            /\
            ( HT029OnCircle B S x )
          )
      )
    )
  ) $.
$}

hundred-theorems-029-feuerbach $a |- (
  (
    (
      (
        (
          (
            ( A e. HT029Plane /\ B e. HT029Plane )
            /\
            C e. HT029Plane
          )
          /\
          (
            ( D e. HT029Plane /\ E e. HT029Plane )
            /\
            F e. HT029Plane
          )
        )
        /\
        (
          (
            ( G e. HT029Plane /\ H e. HT029Plane )
            /\
            I e. HT029Plane
          )
          /\
          ( J e. HT029Plane /\ K e. HT029Plane )
        )
      )
      /\
      ( R e. RR /\ S e. RR )
    )
    /\
    (
      -. ( HT029Collinear A B C )
      /\
      (
        ( HT029Midpoint A B F )
        /\
        (
          ( HT029Midpoint B C D )
          /\
          (
            ( HT029Midpoint C A E )
            /\
            (
              ( HT029OnCircle J R D )
              /\
              (
                ( HT029OnCircle J R E )
                /\
                (
                  ( HT029OnCircle J R F )
                  /\
                  (
                    ( HT029OnCircle K S G )
                    /\
                    (
                      ( HT029OnCircle K S H )
                      /\
                      (
                        ( HT029OnCircle K S I )
                        /\
                        (
                          (
                            ( HT029Collinear A B I )
                            /\
                            ( HT029Perpendicular A B K I )
                          )
                          /\
                          (
                            (
                              ( HT029Collinear B C G )
                              /\
                              ( HT029Perpendicular B C K G )
                            )
                            /\
                            (
                              ( HT029Collinear A C H )
                              /\
                              ( HT029Perpendicular A C K H )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
  ->
  ( HT029CirclesTangent J R K S )
) $.
