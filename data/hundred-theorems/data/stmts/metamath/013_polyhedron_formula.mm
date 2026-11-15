$(
  Statement-only formalization of "Polyhedron Formula" from Hundred
  Theorems item 013: every full-dimensional convex polytope in real
  three-space satisfies Euler's vertex-edge-face equation V + F - E = 2.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Real three-space is represented by RR X. ( RR X. RR ).  The following
  symbols are definitional abbreviations only.  They expand convex
  polytopes as convex hulls of internally existentially quantified finite
  sets of real points, faces by the open-segment characterization, and
  affine dimensions by affine independence of two, three, or four points.
$)

$c
  HT013R3 HT013X HT013Y HT013Z HT013Mix HT013Hull HT013Convex
  HT013AI3 HT013Det HT013AI4 HT013Dim0 HT013Dim1 HT013Dim2
  HT013Full3 HT013Polytope HT013Face HT013Faces0 HT013Faces1
  HT013Faces2
$.

ht013-r3-syntax $a class HT013R3 $.
ht013-x-syntax $a class ( HT013X A ) $.
ht013-y-syntax $a class ( HT013Y A ) $.
ht013-z-syntax $a class ( HT013Z A ) $.
ht013-mix-syntax $a class ( A HT013Mix B C ) $.
ht013-hull-syntax $a class ( HT013Hull A ) $.
ht013-convex-syntax $a wff ( HT013Convex A ) $.
ht013-ai3-syntax $a wff ( HT013AI3 A B C ) $.
ht013-det-syntax $a class ( HT013Det A B C D ) $.
ht013-ai4-syntax $a wff ( HT013AI4 A B C D ) $.
ht013-dim0-syntax $a wff ( HT013Dim0 A ) $.
ht013-dim1-syntax $a wff ( HT013Dim1 A ) $.
ht013-dim2-syntax $a wff ( HT013Dim2 A ) $.
ht013-full3-syntax $a wff ( HT013Full3 A ) $.
ht013-polytope-syntax $a wff ( HT013Polytope A ) $.
ht013-face-syntax $a wff ( A HT013Face B ) $.
ht013-faces0-syntax $a class ( HT013Faces0 A ) $.
ht013-faces1-syntax $a class ( HT013Faces1 A ) $.
ht013-faces2-syntax $a class ( HT013Faces2 A ) $.

ht013-r3-def $a
  |- HT013R3 = ( RR X. ( RR X. RR ) )
$.

ht013-x-def $a
  |- ( HT013X A ) = ( 1st ` A )
$.

ht013-y-def $a
  |- ( HT013Y A ) = ( 1st ` ( 2nd ` A ) )
$.

ht013-z-def $a
  |- ( HT013Z A ) = ( 2nd ` ( 2nd ` A ) )
$.

ht013-mix-def $a
  |- ( A HT013Mix B C ) =
      <. ( ( 1 - A ) x. ( HT013X B ) ) + ( A x. ( HT013X C ) ) ,
        <. ( ( 1 - A ) x. ( HT013Y B ) ) + ( A x. ( HT013Y C ) ) ,
           ( ( 1 - A ) x. ( HT013Z B ) ) + ( A x. ( HT013Z C ) ) >. >.
$.

${
  $d w x z A $.
  ht013-hull-def $a
    |- ( HT013Hull A ) =
       { z e. HT013R3 |
         E. w
           ( ( w : A --> RR /\
               A. x e. A ( 0 <_ ( w ` x ) ) ) /\
             ( ( sum_ x e. A ( w ` x ) ) = 1 /\
               z =
               <. sum_ x e. A ( ( w ` x ) x. ( HT013X x ) ) ,
                  <. sum_ x e. A ( ( w ` x ) x. ( HT013Y x ) ) ,
                     sum_ x e. A ( ( w ` x ) x. ( HT013Z x ) ) >. >. ) ) }
  $.
$}

${
  $d t x y A $.
  ht013-convex-def $a
    |- ( HT013Convex A ) <->
       A. x e. A A. y e. A A. t e. RR
         ( ( 0 <_ t /\ t <_ 1 ) -> ( ( t HT013Mix x y ) e. A ) )
  $.
$}

ht013-ai3-def $a
  |- ( HT013AI3 A B C ) <->
     ( ( ( ( HT013X B ) - ( HT013X A ) ) x.
           ( ( HT013Y C ) - ( HT013Y A ) ) ) =/=
         ( ( ( HT013Y B ) - ( HT013Y A ) ) x.
           ( ( HT013X C ) - ( HT013X A ) ) ) \/
       ( ( ( HT013X B ) - ( HT013X A ) ) x.
           ( ( HT013Z C ) - ( HT013Z A ) ) ) =/=
         ( ( ( HT013Z B ) - ( HT013Z A ) ) x.
           ( ( HT013X C ) - ( HT013X A ) ) ) \/
       ( ( ( HT013Y B ) - ( HT013Y A ) ) x.
           ( ( HT013Z C ) - ( HT013Z A ) ) ) =/=
         ( ( ( HT013Z B ) - ( HT013Z A ) ) x.
           ( ( HT013Y C ) - ( HT013Y A ) ) ) )
$.

ht013-det-def $a
  |- ( HT013Det A B C D ) =
     ( ( ( ( HT013X B ) - ( HT013X A ) ) x.
         ( ( ( ( HT013Y C ) - ( HT013Y A ) ) x.
             ( ( HT013Z D ) - ( HT013Z A ) ) ) -
           ( ( ( HT013Z C ) - ( HT013Z A ) ) x.
             ( ( HT013Y D ) - ( HT013Y A ) ) ) ) ) -
       ( ( ( HT013Y B ) - ( HT013Y A ) ) x.
         ( ( ( ( HT013X C ) - ( HT013X A ) ) x.
             ( ( HT013Z D ) - ( HT013Z A ) ) ) -
           ( ( ( HT013Z C ) - ( HT013Z A ) ) x.
             ( ( HT013X D ) - ( HT013X A ) ) ) ) ) ) +
       ( ( ( HT013Z B ) - ( HT013Z A ) ) x.
         ( ( ( ( HT013X C ) - ( HT013X A ) ) x.
             ( ( HT013Y D ) - ( HT013Y A ) ) ) -
           ( ( ( HT013Y C ) - ( HT013Y A ) ) x.
             ( ( HT013X D ) - ( HT013X A ) ) ) ) ) )
$.

ht013-ai4-def $a
  |- ( HT013AI4 A B C D ) <-> ( ( HT013Det A B C D ) =/= 0 )
$.

${
  $d x y A $.
  ht013-dim0-def $a
    |- ( HT013Dim0 A ) <->
       ( ( A C_ HT013R3 /\ A =/= (/) ) /\
         A. x e. A A. y e. A x = y )
  $.
$}

${
  $d x y z A $.
  ht013-dim1-def $a
    |- ( HT013Dim1 A ) <->
       ( ( A C_ HT013R3 /\
           E. x e. A E. y e. A x =/= y ) /\
         A. x e. A A. y e. A A. z e. A
           -. ( HT013AI3 x y z ) )
  $.
$}

${
  $d w x y z A $.
  ht013-dim2-def $a
    |- ( HT013Dim2 A ) <->
       ( ( A C_ HT013R3 /\
           E. x e. A E. y e. A E. z e. A
             ( HT013AI3 x y z ) ) /\
         A. w e. A A. x e. A A. y e. A A. z e. A
           -. ( HT013AI4 w x y z ) )
  $.
$}

${
  $d w x y z A $.
  ht013-full3-def $a
    |- ( HT013Full3 A ) <->
       ( A C_ HT013R3 /\
         E. w e. A E. x e. A E. y e. A E. z e. A
           ( HT013AI4 w x y z ) )
  $.
$}

${
  $d v A $.
  ht013-polytope-def $a
    |- ( HT013Polytope A ) <->
       E. v
         ( ( v e. Fin /\ v C_ HT013R3 ) /\
           A = ( HT013Hull v ) )
  $.
$}

${
  $d t x y A B $.
  ht013-face-def $a
    |- ( A HT013Face B ) <->
       ( ( A C_ B /\ ( HT013Convex A ) ) /\
         A. x e. B A. y e. B A. t e. RR
           ( ( ( 0 < t /\ t < 1 ) /\
               ( ( t HT013Mix x y ) e. A ) ) ->
             ( x e. A /\ y e. A ) ) )
  $.
$}

${
  $d f A $.
  ht013-faces0-def $a
    |- ( HT013Faces0 A ) =
       { f e. ~P A | ( ( f HT013Face A ) /\ ( HT013Dim0 f ) ) }
  $.

  ht013-faces1-def $a
    |- ( HT013Faces1 A ) =
       { f e. ~P A | ( ( f HT013Face A ) /\ ( HT013Dim1 f ) ) }
  $.

  ht013-faces2-def $a
    |- ( HT013Faces2 A ) =
       { f e. ~P A | ( ( f HT013Face A ) /\ ( HT013Dim2 f ) ) }
  $.
$}

$(
  This unproved assertion is the translated statement.  The cardinalities
  count the zero-, one-, and two-dimensional faces, respectively; subtraction
  is natural-number subtraction, matching the HOL Light and Isabelle sources.
$)
ht013-polyhedron-formula $a
  |- A. p
       ( ( ( HT013Polytope p ) /\ ( HT013Full3 p ) ) ->
         ( ( ( # ` ( HT013Faces0 p ) ) +
             ( # ` ( HT013Faces2 p ) ) ) -
           ( # ` ( HT013Faces1 p ) ) ) = 2 )
$.
