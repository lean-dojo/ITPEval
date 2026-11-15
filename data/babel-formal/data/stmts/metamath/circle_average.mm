$(
  Statement-only formalization of the Babel-formal topic circle_average. This file contains no
  proof.
$)

$(
  Statement-only encoding of the circle-average theory.

  obj is the fixed abstract carrier R, and fun is the function sort R -> R.
  forallObj, forallFun, and lambda are object-language binders.  The operation
  symbols zero, add, and integral are fixed by the surrounding abstract
  structure.  Every mathematical law and claim below is an unproved axiomatic
  assertion.
$)

$c ovar fvar obj fun wff |- ( ) lambda @ forallObj forallFun = ->
   zero add integral circleMap circleAverage $.

$v x y z theta c d k f g h u v qfun ph ps $.

bx     $f ovar x $.
by     $f ovar y $.
bz     $f ovar z $.
btheta $f ovar theta $.
bc     $f ovar c $.
bd     $f ovar d $.
bk     $f ovar k $.
bf     $f fvar f $.
bg     $f fvar g $.
bh     $f fvar h $.
vu     $f obj u $.
vv     $f obj v $.
vqfun  $f fun qfun $.
vph    $f wff ph $.
vps    $f wff ps $.

objVarTerm        $a obj x $.
funVarTerm        $a fun f $.
zeroTerm          $a obj zero $.
addTerm           $a obj ( add u v ) $.
applyTerm         $a obj ( qfun @ u ) $.
lambdaTerm        $a fun ( lambda x u ) $.
integralTerm      $a obj ( integral qfun ) $.
circleMapTerm     $a obj ( circleMap u v ) $.
circleAverageTerm $a obj ( circleAverage qfun u ) $.
equalityFormula   $a wff ( u = v ) $.
implicationFormula $a wff ( ph -> ps ) $.
forallObjFormula  $a wff ( forallObj x ph ) $.
forallFunFormula  $a wff ( forallFun f ph ) $.

$d x y z theta c d k f g h $.

addZero $a |- ( forallObj x
  ( ( add x zero ) = x ) ) $.

addComm $a |- ( forallObj x
  ( forallObj y
    ( ( add x y ) = ( add y x ) ) ) ) $.

addAssoc $a |- ( forallObj x
  ( forallObj y
    ( forallObj z
      ( ( add ( add x y ) z ) = ( add x ( add y z ) ) ) ) ) ) $.

integralExt $a |- ( forallFun f
  ( forallFun g
    ( ( forallObj theta
        ( ( f @ theta ) = ( g @ theta ) ) )
      ->
      ( ( integral f ) = ( integral g ) ) ) ) ) $.

integralConst $a |- ( forallObj c
  ( ( integral ( lambda theta c ) ) = c ) ) $.

integralAdd $a |- ( forallFun f
  ( forallFun g
    ( ( integral
          ( lambda theta ( add ( f @ theta ) ( g @ theta ) ) ) )
      =
      ( add ( integral f ) ( integral g ) ) ) ) ) $.

integralShift $a |- ( forallFun f
  ( forallObj c
    ( ( integral
          ( lambda theta ( f @ ( add theta c ) ) ) )
      =
      ( integral f ) ) ) ) $.

circleMapDef $a |- ( forallObj c
  ( forallObj theta
    ( ( circleMap c theta ) = ( add theta c ) ) ) ) $.

circleAverageDef $a |- ( forallFun f
  ( forallObj c
    ( ( circleAverage f c )
      =
      ( integral
        ( lambda theta ( f @ ( circleMap c theta ) ) ) ) ) ) ) $.

circleMapZero $a |- ( forallObj theta
  ( ( circleMap zero theta ) = theta ) ) $.

circleAverageZero $a |- ( forallFun f
  ( ( circleAverage f zero ) = ( integral f ) ) ) $.

circleAverageAdd $a |- ( forallFun f
  ( forallFun g
    ( forallObj c
      ( ( circleAverage
            ( lambda z ( add ( f @ z ) ( g @ z ) ) )
            c )
        =
        ( add
          ( circleAverage f c )
          ( circleAverage g c ) ) ) ) ) ) $.

circleAverageFunAdd $a |- ( forallFun f
  ( forallObj c
    ( ( circleAverage
          ( lambda z ( f @ ( add z c ) ) )
          zero )
      =
      ( circleAverage f c ) ) ) ) $.

circleMapAdd $a |- ( forallObj c
  ( forallObj d
    ( forallObj theta
      ( ( circleMap ( add c d ) theta )
        =
        ( circleMap c ( circleMap d theta ) ) ) ) ) ) $.

circleAverageShift $a |- ( forallFun f
  ( forallObj c
    ( forallObj d
      ( ( circleAverage f ( add c d ) )
        =
        ( circleAverage
          ( lambda z ( f @ ( add z d ) ) )
          c ) ) ) ) ) $.

circleAverageConst $a |- ( forallObj k
  ( forallObj c
    ( ( circleAverage ( lambda z k ) c ) = k ) ) ) $.

circleAverageAddConst $a |- ( forallFun f
  ( forallObj k
    ( forallObj c
      ( ( circleAverage
            ( lambda z ( add ( f @ z ) k ) )
            c )
        =
        ( add ( circleAverage f c ) k ) ) ) ) ) $.

circleAverageCommAdd $a |- ( forallFun f
  ( forallFun g
    ( forallObj c
      ( ( circleAverage
            ( lambda z ( add ( f @ z ) ( g @ z ) ) )
            c )
        =
        ( circleAverage
          ( lambda z ( add ( g @ z ) ( f @ z ) ) )
          c ) ) ) ) ) $.

circleAverageAddAssoc $a |- ( forallFun f
  ( forallFun g
    ( forallFun h
      ( forallObj c
        ( ( circleAverage
              ( lambda z
                ( add ( add ( f @ z ) ( g @ z ) ) ( h @ z ) ) )
              c )
          =
          ( add
            ( circleAverage f c )
            ( add
              ( circleAverage g c )
              ( circleAverage h c ) ) ) ) ) ) ) ) $.

circleAverageCenterComm $a |- ( forallFun f
  ( forallObj c
    ( forallObj d
      ( ( circleAverage f ( add c d ) )
        =
        ( circleAverage f ( add d c ) ) ) ) ) ) $.

circleAverageCenterIndependent $a |- ( forallFun f
  ( forallObj c
    ( ( circleAverage f c ) = ( integral f ) ) ) ) $.

circleAverageCenterEq $a |- ( forallFun f
  ( forallObj c
    ( forallObj d
      ( ( circleAverage f c ) = ( circleAverage f d ) ) ) ) ) $.

circleAverageIdempotent $a |- ( forallFun f
  ( forallObj c
    ( ( circleAverage
          ( lambda z ( circleAverage f z ) )
          c )
      =
      ( circleAverage f c ) ) ) ) $.

circleAverageOfZeroIntegral $a |- ( forallFun f
  ( forallObj c
    ( ( ( integral f ) = zero )
      ->
      ( ( circleAverage f c ) = zero ) ) ) ) $.

circleAverageLinear $a |- ( forallFun f
  ( forallFun g
    ( forallObj c
      ( ( circleAverage
            ( lambda z ( add ( f @ z ) ( g @ z ) ) )
            c )
        =
        ( add
          ( circleAverage f c )
          ( circleAverage g c ) ) ) ) ) ) $.

circleAverageShiftCommute $a |- ( forallFun f
  ( forallObj c
    ( forallObj d
      ( ( circleAverage
            ( lambda z ( f @ ( circleMap d z ) ) )
            c )
        =
        ( circleAverage f ( add c d ) ) ) ) ) ) $.
