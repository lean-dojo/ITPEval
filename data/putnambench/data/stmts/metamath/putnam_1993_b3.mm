$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_b3: the planar Lebesgue
  measure of points in the open unit square for which the nearest
  integer to the coordinate ratio is even is expressed by a rational
  pair and pi.  This file contains no proof.

  The two coordinates are indexed by { 0 , 1 }, corresponding to the
  source type Fin 2.  Nearest-integer rounding is rendered as
  floor ( x + 1 / 2 ), and evenness is rendered by an internally
  quantified integer multiplier. The resolved rational pair is substituted
  directly as ( 5 / 4 , -1 / 4 ).
$)

$[ lib/set.mm $]

$c P93B3I P93B3Plane P93B3Event P93B3Area $.

p93b3-index-syntax $a class P93B3I $.
p93b3-plane-syntax $a class P93B3Plane $.
p93b3-event-syntax $a class P93B3Event $.
p93b3-area-syntax $a class P93B3Area $.

p93b3-index-definition $a
  |- P93B3I = ( 0 ... 1 ) $.

p93b3-plane-definition $a
  |- P93B3Plane = ( RR ^m P93B3I ) $.

${
  $d i k p $.
  p93b3-event-definition $a
    |- P93B3Event =
        { p e. P93B3Plane |
          ( A. i e. P93B3I
              ( 0 < ( p ` i ) /\ ( p ` i ) < 1 )
            /\
            E. k e. ZZ
              ( |_ ` ( ( ( p ` 0 ) / ( p ` 1 ) ) + ( 1 / 2 ) ) )
                =
              ( 2 x. k ) ) } $.
$}

p93b3-area-definition $a
  |- P93B3Area = ( ( voln ` P93B3I ) ` P93B3Event ) $.

putnambench-putnam-1993-b3 $a
  |- P93B3Area =
      ( ( 5 / 4 ) + ( ( -u 1 / 4 ) x. _pi ) ) $.
