$(
  Statement-only formalization of "The Number of Platonic Solids" from
  Hundred Theorems item 050: a full-dimensional convex polytope in real
  three-space has uniform facet-edge and vertex-edge incidence counts
  exactly for the five classical Platonic pairs.  This file contains no
  proof.
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
  HT050R3 HT050X HT050Y HT050Z HT050Mix HT050Hull HT050Convex
  HT050AI3 HT050Det HT050AI4 HT050Dim0 HT050Dim1 HT050Dim2
  HT050Full3 HT050Polytope HT050Face HT050EdgesInFace
  HT050EdgesAtVertex
$.

ht050-r3-syntax $a class HT050R3 $.
ht050-x-syntax $a class ( HT050X A ) $.
ht050-y-syntax $a class ( HT050Y A ) $.
ht050-z-syntax $a class ( HT050Z A ) $.
ht050-mix-syntax $a class ( A HT050Mix B C ) $.
ht050-hull-syntax $a class ( HT050Hull A ) $.
ht050-convex-syntax $a wff ( HT050Convex A ) $.
ht050-ai3-syntax $a wff ( HT050AI3 A B C ) $.
ht050-det-syntax $a class ( HT050Det A B C D ) $.
ht050-ai4-syntax $a wff ( HT050AI4 A B C D ) $.
ht050-dim0-syntax $a wff ( HT050Dim0 A ) $.
ht050-dim1-syntax $a wff ( HT050Dim1 A ) $.
ht050-dim2-syntax $a wff ( HT050Dim2 A ) $.
ht050-full3-syntax $a wff ( HT050Full3 A ) $.
ht050-polytope-syntax $a wff ( HT050Polytope A ) $.
ht050-face-syntax $a wff ( A HT050Face B ) $.
ht050-edges-in-face-syntax $a class ( HT050EdgesInFace A B ) $.
ht050-edges-at-vertex-syntax $a class ( HT050EdgesAtVertex A B ) $.

ht050-r3-def $a
  |- HT050R3 = ( RR X. ( RR X. RR ) )
$.

ht050-x-def $a
  |- ( HT050X A ) = ( 1st ` A )
$.

ht050-y-def $a
  |- ( HT050Y A ) = ( 1st ` ( 2nd ` A ) )
$.

ht050-z-def $a
  |- ( HT050Z A ) = ( 2nd ` ( 2nd ` A ) )
$.

ht050-mix-def $a
  |- ( A HT050Mix B C ) =
      <. ( ( 1 - A ) x. ( HT050X B ) ) + ( A x. ( HT050X C ) ) ,
        <. ( ( 1 - A ) x. ( HT050Y B ) ) + ( A x. ( HT050Y C ) ) ,
           ( ( 1 - A ) x. ( HT050Z B ) ) + ( A x. ( HT050Z C ) ) >. >.
$.

${
  $d w x z A $.
  ht050-hull-def $a
    |- ( HT050Hull A ) =
       { z e. HT050R3 |
         E. w
           ( ( w : A --> RR /\
               A. x e. A ( 0 <_ ( w ` x ) ) ) /\
             ( ( sum_ x e. A ( w ` x ) ) = 1 /\
               z =
               <. sum_ x e. A ( ( w ` x ) x. ( HT050X x ) ) ,
                  <. sum_ x e. A ( ( w ` x ) x. ( HT050Y x ) ) ,
                     sum_ x e. A ( ( w ` x ) x. ( HT050Z x ) ) >. >. ) ) }
  $.
$}

${
  $d t x y A $.
  ht050-convex-def $a
    |- ( HT050Convex A ) <->
       A. x e. A A. y e. A A. t e. RR
         ( ( 0 <_ t /\ t <_ 1 ) -> ( ( t HT050Mix x y ) e. A ) )
  $.
$}

ht050-ai3-def $a
  |- ( HT050AI3 A B C ) <->
     ( ( ( ( HT050X B ) - ( HT050X A ) ) x.
           ( ( HT050Y C ) - ( HT050Y A ) ) ) =/=
         ( ( ( HT050Y B ) - ( HT050Y A ) ) x.
           ( ( HT050X C ) - ( HT050X A ) ) ) \/
       ( ( ( HT050X B ) - ( HT050X A ) ) x.
           ( ( HT050Z C ) - ( HT050Z A ) ) ) =/=
         ( ( ( HT050Z B ) - ( HT050Z A ) ) x.
           ( ( HT050X C ) - ( HT050X A ) ) ) \/
       ( ( ( HT050Y B ) - ( HT050Y A ) ) x.
           ( ( HT050Z C ) - ( HT050Z A ) ) ) =/=
         ( ( ( HT050Z B ) - ( HT050Z A ) ) x.
           ( ( HT050Y C ) - ( HT050Y A ) ) ) )
$.

ht050-det-def $a
  |- ( HT050Det A B C D ) =
     ( ( ( ( HT050X B ) - ( HT050X A ) ) x.
         ( ( ( ( HT050Y C ) - ( HT050Y A ) ) x.
             ( ( HT050Z D ) - ( HT050Z A ) ) ) -
           ( ( ( HT050Z C ) - ( HT050Z A ) ) x.
             ( ( HT050Y D ) - ( HT050Y A ) ) ) ) ) -
       ( ( ( HT050Y B ) - ( HT050Y A ) ) x.
         ( ( ( ( HT050X C ) - ( HT050X A ) ) x.
             ( ( HT050Z D ) - ( HT050Z A ) ) ) -
           ( ( ( HT050Z C ) - ( HT050Z A ) ) x.
             ( ( HT050X D ) - ( HT050X A ) ) ) ) ) ) +
       ( ( ( HT050Z B ) - ( HT050Z A ) ) x.
         ( ( ( ( HT050X C ) - ( HT050X A ) ) x.
             ( ( HT050Y D ) - ( HT050Y A ) ) ) -
           ( ( ( HT050Y C ) - ( HT050Y A ) ) x.
             ( ( HT050X D ) - ( HT050X A ) ) ) ) ) )
$.

ht050-ai4-def $a
  |- ( HT050AI4 A B C D ) <-> ( ( HT050Det A B C D ) =/= 0 )
$.

${
  $d x y A $.
  ht050-dim0-def $a
    |- ( HT050Dim0 A ) <->
       ( ( A C_ HT050R3 /\ A =/= (/) ) /\
         A. x e. A A. y e. A x = y )
  $.
$}

${
  $d x y z A $.
  ht050-dim1-def $a
    |- ( HT050Dim1 A ) <->
       ( ( A C_ HT050R3 /\
           E. x e. A E. y e. A x =/= y ) /\
         A. x e. A A. y e. A A. z e. A
           -. ( HT050AI3 x y z ) )
  $.
$}

${
  $d w x y z A $.
  ht050-dim2-def $a
    |- ( HT050Dim2 A ) <->
       ( ( A C_ HT050R3 /\
           E. x e. A E. y e. A E. z e. A
             ( HT050AI3 x y z ) ) /\
         A. w e. A A. x e. A A. y e. A A. z e. A
           -. ( HT050AI4 w x y z ) )
  $.
$}

${
  $d w x y z A $.
  ht050-full3-def $a
    |- ( HT050Full3 A ) <->
       ( A C_ HT050R3 /\
         E. w e. A E. x e. A E. y e. A E. z e. A
           ( HT050AI4 w x y z ) )
  $.
$}

${
  $d v A $.
  ht050-polytope-def $a
    |- ( HT050Polytope A ) <->
       E. v
         ( ( v e. Fin /\ v C_ HT050R3 ) /\
           A = ( HT050Hull v ) )
  $.
$}

${
  $d t x y A B $.
  ht050-face-def $a
    |- ( A HT050Face B ) <->
       ( ( A C_ B /\ ( HT050Convex A ) ) /\
         A. x e. B A. y e. B A. t e. RR
           ( ( ( 0 < t /\ t < 1 ) /\
               ( ( t HT050Mix x y ) e. A ) ) ->
             ( x e. A /\ y e. A ) ) )
  $.
$}

${
  $d e A B $.
  ht050-edges-in-face-def $a
    |- ( HT050EdgesInFace A B ) =
       { e e. ~P A |
         ( ( e HT050Face A ) /\
           ( ( HT050Dim1 e ) /\ e C_ B ) ) }
  $.

  ht050-edges-at-vertex-def $a
    |- ( HT050EdgesAtVertex A B ) =
       { e e. ~P A |
         ( ( e HT050Face A ) /\
           ( ( HT050Dim1 e ) /\ B C_ e ) ) }
  $.
$}

$(
  This unproved assertion is the translated statement.  The two set
  comprehensions are the one-dimensional faces of p contained in a facet f
  and containing a vertex v, respectively.  Their set.mm cardinalities are
  finite for the finite convex-hull polytopes defined above.
$)
ht050-platonic-solids $a
  |- A. m e. NN0 A. n e. NN0
       ( E. p
           ( ( ( HT050Polytope p ) /\ ( HT050Full3 p ) ) /\
             ( A. f
                 ( ( ( f HT050Face p ) /\ ( HT050Dim2 f ) ) ->
                   ( ( # ` ( HT050EdgesInFace p f ) ) = m ) ) /\
               A. v
                 ( ( ( v HT050Face p ) /\ ( HT050Dim0 v ) ) ->
                   ( ( # ` ( HT050EdgesAtVertex p v ) ) = n ) ) ) )
         <->
         ( ( m = 3 /\ n = 3 ) \/
           ( ( m = 4 /\ n = 3 ) \/
             ( ( m = 3 /\ n = 4 ) \/
               ( ( m = 5 /\ n = 3 ) \/
                 ( m = 3 /\ n = 5 ) ) ) ) ) )
$.
