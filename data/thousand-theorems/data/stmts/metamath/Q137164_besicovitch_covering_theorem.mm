$(
  Statement-only formalization of Thousand Theorems corpus artifact Q137164
  (thousand-theorems__metamath__Q137164), "Besicovitch covering theorem": in
  a second-countable metric space with measurable open sets and the
  Besicovitch covering property, every family of admissible radii available
  at arbitrarily small positive scales admits, for any s-finite measure, a
  countable pairwise-disjoint closed-ball subfamily covering the given set
  almost everywhere. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q137164ClosedBall is the metric closed ball. Q137164Satellite expands the
  finite satellite configurations excluded by the source's Besicovitch
  covering property. Q137164SFinite states that a measure is a countable sum
  of finite measures on the same measurable space. Q137164Measure evaluates
  the outer measure induced by a measure, retaining the source theorem's
  application to arbitrary, not necessarily measurable, sets.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or bidirectional definitions, and
  there are no $p declarations in this file.
$)

$c Q137164ClosedBall Q137164Satellite Q137164HasBesicovitch
   Q137164SFinite Q137164Measure $.

$( The closed metric ball with center x and radius a in the carrier X. $)
q137164-wclosedball $a
  class ( Q137164ClosedBall D X x a ) $.

${
  $d D X x y a $.
  q137164-df-closedball $a
    |- ( Q137164ClosedBall D X x a ) =
       { y e. X | ( x D y ) <_ a } $.
$}

$( A finite satellite configuration, with indices 0 through N. $)
q137164-wsatellite $a
  wff ( Q137164Satellite D X N t c r ) $.

${
  $d D X N t c r i j $.
  q137164-df-satellite $a
    |- ( ( Q137164Satellite D X N t c r ) <->
         ( c e. ( X ^m ( 0 ..^ ( N + 1 ) ) ) /\
           ( r e. ( RR ^m ( 0 ..^ ( N + 1 ) ) ) /\
             ( A. i e. ( 0 ..^ ( N + 1 ) ) 0 < ( r ` i ) /\
               ( A. i e. ( 0 ..^ ( N + 1 ) )
                 A. j e. ( 0 ..^ ( N + 1 ) )
                   ( i =/= j ->
                     ( ( ( r ` i ) <_ ( ( c ` i ) D ( c ` j ) ) /\
                         ( r ` j ) <_ ( t x. ( r ` i ) ) ) \/
                       ( ( r ` j ) <_ ( ( c ` j ) D ( c ` i ) ) /\
                         ( r ` i ) <_ ( t x. ( r ` j ) ) ) ) ) /\
                 ( A. i e. ( 0 ..^ N )
                     ( ( r ` i ) <_ ( ( c ` i ) D ( c ` N ) ) /\
                       ( r ` N ) <_ ( t x. ( r ` i ) ) ) /\
                   A. i e. ( 0 ..^ N )
                     ( ( ( c ` i ) D ( c ` N ) ) <_
                       ( ( r ` i ) + ( r ` N ) ) ) ) ) ) ) ) ) $.
$}

$( The Besicovitch covering property, expressed by the absence of a
   sufficiently large finite satellite configuration. $)
q137164-whasbesicovitch $a
  wff ( Q137164HasBesicovitch D X ) $.

${
  $d D X c q r t $.
  q137164-df-hasbesicovitch $a
    |- ( ( Q137164HasBesicovitch D X ) <->
         E. q e. NN0 E. t e. RR
           ( 1 < t /\
             -. E. c e. ( X ^m ( 0 ..^ ( q + 1 ) ) )
                E. r e. ( RR ^m ( 0 ..^ ( q + 1 ) ) )
                  ( Q137164Satellite D X q t c r ) ) ) $.
$}

$( S-finiteness: a measure is a countable sum of finite measures on the
   same measurable space. $)
q137164-wsfinite $a
  wff ( Q137164SFinite M ) $.

${
  $d M a f n $.
  q137164-df-sfinite $a
    |- ( ( Q137164SFinite M ) <->
         E. f
           ( f Fn NN0 /\
             ( ( A. n e. NN0
                   ( ( f ` n ) e. U. ran measures /\
                     ( dom ( f ` n ) = dom M /\
                       ( ( f ` n ) ` U. dom M ) < +oo ) ) ) /\
               A. a e. dom M
                 ( M ` a ) =
                 ( sum^ ` ( n e. NN0 |-> ( ( f ` n ) ` a ) ) ) ) ) ) $.
$}

$( Evaluation of the outer measure canonically associated with M. $)
q137164-wmeasure $a
  class ( Q137164Measure M A ) $.

${
  $d M A $.
  q137164-df-measure $a
    |- ( Q137164Measure M A ) = ( ( toOMeas ` M ) ` A ) $.
$}

${
  $d a d f g m p r s t x y $.

  thousand-theorems-q137164-besicovitch-covering-theorem $a
    |- A. m e. U. ran measures
         A. p A. f A. s A. g
           ( ( p e. ( Met ` U. dom m ) /\
               ( ( MetOpen ` p ) e. 2ndc /\
                 ( ( MetOpen ` p ) C_ dom m /\
                   ( ( Q137164SFinite m ) /\
                     ( Q137164HasBesicovitch p ( U. dom m ) ) ) ) ) ) ->
             ( ( f e. ( ( ~P RR ) ^m ( U. dom m ) ) /\
                 ( s C_ U. dom m /\
                   g e. ( RR ^m ( U. dom m ) ) ) ) ->
               ( ( ( A. x e. s A. d e. RR+
                       E. a e. ( f ` x ) ( 0 < a /\ a < d ) ) /\
                   A. x e. s 0 < ( g ` x ) ) ->
                 E. t e. ~P ( U. dom m )
                   E. r e. ( RR ^m ( U. dom m ) )
                     ( t ~<_ NN0 /\
                       ( t C_ s /\
                         ( A. x e. t
                             ( ( r ` x ) e. ( f ` x ) /\
                               ( 0 < ( r ` x ) /\
                                 ( r ` x ) < ( g ` x ) ) ) /\
                           ( ( Q137164Measure m
                                 ( s \ U_ x e. t
                                     ( Q137164ClosedBall
                                       p ( U. dom m ) x ( r ` x ) ) ) ) = 0 /\
                             A. x e. t A. y e. t
                               ( x =/= y ->
                                 ( ( Q137164ClosedBall
                                       p ( U. dom m ) x ( r ` x ) ) i^i
                                   ( Q137164ClosedBall
                                       p ( U. dom m ) y ( r ` y ) ) ) =
                                 (/) ) ) ) ) ) ) ) ) ) ) $.
$}
